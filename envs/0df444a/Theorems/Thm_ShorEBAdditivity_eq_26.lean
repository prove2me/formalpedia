-- Prove2me | Theorems.Thm_ShorEBAdditivity_eq_26
-- name    : ShorEBAdditivity.eq_26
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T03:19:12.11929+00:00
-- url     : https://prove2.me/theorems/690eae21-9db6-4c9a-817b-2023a68c1039
-- title:
--   Eq. (26): $\chi(\{p_i,\rho_i\};\Psi\otimes\Phi) \le H(\Psi(\mathrm{Tr}_B\rho)) + H(\Phi(\mathrm{Tr}_A\rho)) - \sum_{i,j} p_iq_{ij}H(\Psi(\tau_{ij})) - \sum_i p_iH(\Phi(\mathrm{Tr}_A\rho_i))$
-- statement:
--   Let $\Psi : M_A\to M_{A'}$ and $\Phi : M_B\to M_{B'}$ be quantum channels and $\{p_i,\rho_i\}$ a finite ensemble of density matrices on $\mathcal H_A\otimes\mathcal H_B$ with average $\rho = \sum_i p_i\rho_i$. Suppose that for every $i$
--
--   $$
--   (I\otimes\Phi)(\rho_i) = \sum_j q_{ij}\,|a_{ij}\rangle\langle a_{ij}|\otimes|b_{ij}\rangle\langle b_{ij}|
--   $$
--
--   with $q_{ij}\ge 0$ and unit vectors $|a_{ij}\rangle$, $|b_{ij}\rangle$ (the decomposition (18)), and write $\tau_{ij} = |a_{ij}\rangle\langle a_{ij}|$. Then
--
--   $$
--   H\big((\Psi\otimes\Phi)(\rho)\big) - \sum_i p_i H\big((\Psi\otimes\Phi)(\rho_i)\big) \le H\big(\Psi(\operatorname{Tr}_B\rho)\big) + H\big(\Phi(\operatorname{Tr}_A\rho)\big) - \sum_{i,j} p_i q_{ij} H\big(\Psi(\tau_{ij})\big) - \sum_i p_i H\big(\Phi(\operatorname{Tr}_A\rho_i)\big).
--   $$
--
--   For an optimal ensemble (17) the left side is $\chi^*(\Psi\otimes\Phi)$, and this is the display (26).
--
--   **Formalization Note** The left side is `holevoChi (tensorChannel Ψ Φ) p ρ`. Partial trace over the second factor is `traceRight`, over the first factor `traceLeft`; $H$ is `vnEntropy` (bits). The $i$-th decomposition has `m i` terms.
--
--   Differences from the source:
--   - generalization: the optimal signal states (17), for which the left side equals χ*(Ψ ⊗ Φ) → every finite ensemble {p_i, ρ_i}, with the Holevo quantity of the ensemble on the left; reason: an optimal ensemble exists (p.1) and is an instance, where the first line of (26) is (17)
--   - generalization: Φ entanglement breaking, with q_ij, |a_ij⟩, |b_ij⟩ from (18) → any channel Φ and any q_ij ≥ 0, unit vectors a_ij, b_ij with (I ⊗ Φ)(ρ_i) = Σ_j q_ij |a_ij⟩⟨a_ij| ⊗ |b_ij⟩⟨b_ij|; reason: (18) is the only use of entanglement breaking in the proof, and eq_18 supplies such a decomposition for every entanglement-breaking channel
--   - encoding: quantum channel (CPTP map) → IsChannel (finite normalized Kraus family); reason: Choi–Kraus; same maps
--   - encoding: H(ρ) = −Tr ρ log ρ, base unspecified → vnEntropy in bits (log₂); reason: both sides scale by the same factor under a change of base
-- source:
--   Shor, Additivity of the Classical Capacity of Entanglement-Breaking Quantum Channels, arXiv:quant-ph/0201149v3, eq. (26), p.4

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_ShorEBAdditivity_tensorChannel
import Definitions.Def_ShorEBAdditivity_IsEnsemble
import Definitions.Def_ShorEBAdditivity_holevoChi

open QAlgorithms
open scoped Kronecker

namespace ShorEBAdditivity

/-- Shor, *Additivity of the Classical Capacity of Entanglement-Breaking Quantum Channels*,
arXiv:quant-ph/0201149v3, eq. (26), p.4: "Using subadditivity of von Neumann entropy and the
above inequality (25), we get that
χ*(Ψ ⊗ Φ) = H((Ψ ⊗ Φ)(ρ)) − Σ_i pi H((Ψ ⊗ Φ)(ρi))
          ≤ H(Ψ(TrBρ)) + H(Φ(TrAρ)) − Σ_{i,j} pi qij H(Ψ(τij)) − Σ_i pi H(Φ(TrAρi))."

Let `Ψ`, `Φ` be channels and `{p_i, ρ_i}` an ensemble of density matrices on `A ⊗ B` with average
`ρ = Σ_i p_i ρ_i`. Suppose each `(I ⊗ Φ)(ρ_i) = Σ_j q_ij |a_ij⟩⟨a_ij| ⊗ |b_ij⟩⟨b_ij|` with
`q_ij ≥ 0` and unit vectors `|a_ij⟩`, `|b_ij⟩` (the decomposition (18)), and write
`τ_ij = |a_ij⟩⟨a_ij|`. Then the Holevo quantity of the ensemble through `Ψ ⊗ Φ`,
`H((Ψ ⊗ Φ)(ρ)) − Σ_i p_i H((Ψ ⊗ Φ)(ρ_i))`, is at most
`H(Ψ(Tr_B ρ)) + H(Φ(Tr_A ρ)) − Σ_{i,j} p_i q_ij H(Ψ(τ_ij)) − Σ_i p_i H(Φ(Tr_A ρ_i))`.

**Formalization Note.** The page states (26) for the optimal signal states (17), for which the
left side is `χ*(Ψ ⊗ Φ)` (the first line of (26) is (17)); here the inequality is stated for every
ensemble, which specializes to the page's at an optimal one. The Holevo quantity is
`holevoChi (tensorChannel Ψ Φ) p ρ`. The decomposition (18) of each `ρ_i` is the hypothesis `hdec`
(entanglement breaking is used in the paper only to obtain it; `eq_18` supplies it); the `i`-th
decomposition has `m i` terms. `Tr_B` (second factor) is `QAlgorithms.traceRight`, `Tr_A` (first
factor) is `QAlgorithms.traceLeft`, `H` is `QAlgorithms.vnEntropy` (bits). -/
theorem eq_26 {A A' B B' : Type*} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A']
    [Fintype B] [DecidableEq B] [Fintype B'] [DecidableEq B']
    (Ψ : Superop A A') (Φ : Superop B B') (hΨ : IsChannel Ψ) (hΦ : IsChannel Φ)
    {n : ℕ} (p : Fin n → ℝ) (ρ : Fin n → Matrix (A × B) (A × B) ℂ) (hens : IsEnsemble p ρ)
    (m : Fin n → ℕ) (q : (i : Fin n) → Fin (m i) → ℝ) (hq : ∀ i j, 0 ≤ q i j)
    (a : (i : Fin n) → Fin (m i) → EuclideanSpace ℂ A) (ha : ∀ i j, ‖a i j‖ = 1)
    (b : (i : Fin n) → Fin (m i) → EuclideanSpace ℂ B') (hb : ∀ i j, ‖b i j‖ = 1)
    (hdec : ∀ i, idTensorSuperop Φ (ρ i) =
      ∑ j, (q i j : ℂ) • (pureDensity (a i j) ⊗ₖ pureDensity (b i j))) :
    holevoChi (tensorChannel Ψ Φ) p ρ ≤
      vnEntropy (Ψ (traceRight (∑ i, (p i : ℂ) • ρ i))) +
          vnEntropy (Φ (traceLeft (∑ i, (p i : ℂ) • ρ i))) -
        ∑ i, ∑ j, p i * q i j * vnEntropy (Ψ (pureDensity (a i j))) -
        ∑ i, p i * vnEntropy (Φ (traceLeft (ρ i))) := by sorry

end ShorEBAdditivity
