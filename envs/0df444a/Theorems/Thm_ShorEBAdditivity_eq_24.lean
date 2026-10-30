-- Prove2me | Theorems.Thm_ShorEBAdditivity_eq_24
-- name    : ShorEBAdditivity.eq_24
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T03:19:23.455038+00:00
-- url     : https://prove2.me/theorems/646b9c2d-37f4-4648-9cd9-06e0477d959a
-- title:
--   Eq. (24): $\mathrm{Tr}_B\rho = \sum_j q_j\tau_j$ and $H((\Psi\otimes\Phi)(\rho)) \ge \sum_j q_jH(\Psi(\tau_j)) + H(\Phi(\mathrm{Tr}_A\rho))$
-- statement:
--   Let $\Psi : M_A\to M_{A'}$ and $\Phi : M_B\to M_{B'}$ be quantum channels and $\rho$ a density matrix on $\mathcal H_A\otimes\mathcal H_B$. Suppose
--
--   $$
--   (I\otimes\Phi)(\rho) = \sum_j q_j\, |a_j\rangle\langle a_j|\otimes|b_j\rangle\langle b_j|
--   $$
--
--   with $q_j\ge 0$ and unit vectors $|a_j\rangle$, $|b_j\rangle$ (the decomposition (18)), and write $\tau_j = |a_j\rangle\langle a_j|$. Then
--
--   1. $\operatorname{Tr}_B\rho = \sum_j q_j\tau_j$, and
--   2. the output entropy of the product channel satisfies
--   $$
--   H\big((\Psi\otimes\Phi)(\rho)\big) \ge \sum_j q_j\, H\big(\Psi(\tau_j)\big) + H\big(\Phi(\operatorname{Tr}_A\rho)\big).
--   $$
--
--   This is the per-state inequality of the proof: averaged over the signal states of an ensemble it bounds the second term of $\chi^*(\Psi\otimes\Phi)$, and the first clause shows that the $\tau_j$, weighted by $q_j$, form an ensemble for $\Psi$ with average state $\operatorname{Tr}_B\rho$.
--
--   **Formalization Note** $\operatorname{Tr}_B$ (trace over the second factor) is `traceRight`, $\operatorname{Tr}_A$ (trace over the first factor) is `traceLeft`; $\Psi\otimes\Phi$ is `tensorChannel Ψ Φ`; the decomposition (18) is the hypothesis `hdec`. Entropy in bits.
--
--   Differences from the source:
--   - generalization: Φ entanglement breaking, with q_ij, |a_ij⟩, |b_ij⟩ from (18) → any channel Φ and any q_j ≥ 0, unit vectors a_j, b_j with (I ⊗ Φ)(ρ) = Σ_j q_j |a_j⟩⟨a_j| ⊗ |b_j⟩⟨b_j|; reason: (18) is the only use of entanglement breaking in the proof, and eq_18 supplies such a decomposition for every entanglement-breaking channel
--   - generalization: ρ_i a signal state of the optimal ensemble (17) → any density matrix ρ on A × B; reason: (24) uses only that ρ_i is a state
--   - encoding: quantum channel (CPTP map) → IsChannel (finite normalized Kraus family); reason: Choi–Kraus; same maps
--   - encoding: H(ρ) = −Tr ρ log ρ, base unspecified → vnEntropy in bits (log₂); reason: both sides scale by the same factor under a change of base
-- source:
--   Shor, Additivity of the Classical Capacity of Entanglement-Breaking Quantum Channels, arXiv:quant-ph/0201149v3, eq. (24), p.4 (with the sentence "Then TrBρi = Σ qijτij")

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_ShorEBAdditivity_tensorChannel

open QAlgorithms
open scoped Kronecker

namespace ShorEBAdditivity

/-- Shor, *Additivity of the Classical Capacity of Entanglement-Breaking Quantum Channels*,
arXiv:quant-ph/0201149v3, eq. (24), p.4: "We let |aij⟩⟨aij| = τij. Then TrBρi = Σ qij τij.
Combining the terms, we observe H((Ψ ⊗ Φ)(ρi)) ≥ Σ_j qij H(Ψ(τij)) + H(Φ(TrAρi))."

Let `Ψ`, `Φ` be channels, `ρ` a density matrix on `A ⊗ B`, and
`(I ⊗ Φ)(ρ) = Σ_j q_j |a_j⟩⟨a_j| ⊗ |b_j⟩⟨b_j|` with `q_j ≥ 0` and unit vectors `|a_j⟩`, `|b_j⟩`
(the decomposition (18)). Write `τ_j = |a_j⟩⟨a_j|`. Then
1. `Tr_B ρ = Σ_j q_j τ_j`, and
2. `H((Ψ ⊗ Φ)(ρ)) ≥ Σ_j q_j H(Ψ(τ_j)) + H(Φ(Tr_A ρ))`.

**Formalization Note.** `Tr_B` (trace over the second factor) is `QAlgorithms.traceRight` and
`Tr_A` (trace over the first factor) is `QAlgorithms.traceLeft`. `Ψ ⊗ Φ` is `tensorChannel Ψ Φ`,
`I ⊗ Φ` is `QAlgorithms.idTensorSuperop Φ`, `H` is `QAlgorithms.vnEntropy` (bits). The
decomposition (18) is the hypothesis `hdec`; entanglement breaking is used in the paper only to
obtain it. -/
theorem eq_24 {A A' B B' : Type*} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A']
    [Fintype B] [DecidableEq B] [Fintype B'] [DecidableEq B']
    (Ψ : Superop A A') (Φ : Superop B B') (hΨ : IsChannel Ψ) (hΦ : IsChannel Φ)
    (ρ : Matrix (A × B) (A × B) ℂ) (hρ : IsDensityMatrix ρ) {m : ℕ} (q : Fin m → ℝ)
    (hq : ∀ j, 0 ≤ q j) (a : Fin m → EuclideanSpace ℂ A) (ha : ∀ j, ‖a j‖ = 1)
    (b : Fin m → EuclideanSpace ℂ B') (hb : ∀ j, ‖b j‖ = 1)
    (hdec : idTensorSuperop Φ ρ = ∑ j, (q j : ℂ) • (pureDensity (a j) ⊗ₖ pureDensity (b j))) :
    traceRight ρ = ∑ j, (q j : ℂ) • pureDensity (a j) ∧
      ∑ j, q j * vnEntropy (Ψ (pureDensity (a j))) + vnEntropy (Φ (traceLeft ρ)) ≤
        vnEntropy (tensorChannel Ψ Φ ρ) := by sorry

end ShorEBAdditivity
