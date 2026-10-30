-- Prove2me | Theorems.Thm_ShorEBAdditivity_eq_22
-- name    : ShorEBAdditivity.eq_22
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T03:18:47.237613+00:00
-- url     : https://prove2.me/theorems/c3f1fbb2-e2bc-4c12-882d-c1312353993d
-- title:
--   Eq. (22) via (13): $\sigma_B = \sum_j q_j|b_j\rangle\langle b_j| = \mathrm{Tr}_A(I\otimes\Phi)(\rho) = \Phi(\mathrm{Tr}_A\rho)$
-- statement:
--   Let $\Psi : M_A\to M_{A'}$ and $\Phi : M_B\to M_{B'}$ be quantum channels and $\rho$ a density matrix on $\mathcal H_A\otimes\mathcal H_B$. Suppose
--
--   $$
--   (I\otimes\Phi)(\rho) = \sum_j q_j\, |a_j\rangle\langle a_j|\otimes|b_j\rangle\langle b_j|
--   $$
--
--   with unit vectors $|a_j\rangle$ (the decomposition (18)), and let $\sigma_{ABC}$ be the flagged state (19). Then the $B$-marginal $\sigma_B$ of $\sigma_{ABC}$ satisfies
--
--   $$
--   \sigma_B = \sum_j q_j |b_j\rangle\langle b_j| = \operatorname{Tr}_A (I\otimes\Phi)(\rho) = \Phi(\operatorname{Tr}_A\rho).
--   $$
--
--   In particular $H(\sigma_B) = H(\Phi(\operatorname{Tr}_A\rho))$, which is (22). This identifies the last term of strong subadditivity (20) with an output entropy of $\Phi$ alone.
--
--   **Formalization Note** $\sigma_B$ is `traceLeft (traceRight (sigmaABC Ψ q a b))` (trace out the flag, then the $A'$ register); the paper's $\operatorname{Tr}_A$ removes the first factor and is `traceLeft`. The decomposition (18) is the hypothesis `hdec`.
--
--   Differences from the source:
--   - generalization: Φ entanglement breaking, with q_ij, |a_ij⟩, |b_ij⟩ from (18) → any channel Φ and any q, b and unit vectors a with (I ⊗ Φ)(ρ) = Σ_j q_j |a_j⟩⟨a_j| ⊗ |b_j⟩⟨b_j|; reason: (18) is the only use of entanglement breaking in the proof, and eq_18 supplies such a decomposition for every entanglement-breaking channel
--   - generalization: ρ_i a signal state of the optimal ensemble (17) → any density matrix ρ on A × B; reason: the identity uses only that ρ_i is a state
--   - generalization: H(σB) = H(Φ(TrAρi)) → the three matrix identities of (13); reason: equal matrices have equal entropy, so this implies (22); (13) is the page's derivation
--   - encoding: quantum channel (CPTP map) → IsChannel (finite normalized Kraus family); reason: Choi–Kraus; same maps
--   - encoding: |j⟩ an orthonormal set (the flag register C) → the standard basis vectors of ℂ^m, |j⟩⟨j| = Matrix.single j j 1 on Fin m; reason: entropy is invariant under the unitary taking one orthonormal set to another; same values
-- source:
--   Shor, Additivity of the Classical Capacity of Entanglement-Breaking Quantum Channels, arXiv:quant-ph/0201149v3, eq. (22), p.4, with eq. (13), p.3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_ShorEBAdditivity_sigmaABC

open QAlgorithms
open scoped Kronecker

namespace ShorEBAdditivity

/-- Shor, *Additivity of the Classical Capacity of Entanglement-Breaking Quantum Channels*,
arXiv:quant-ph/0201149v3, eq. (22), p.4 ("We also have that H(σB) = H(Φ(TrAρi))"), proved
through the three lines of eq. (13), p.3:
`σ_B = Σ_j q_j |b_j⟩⟨b_j| = Tr_A (I ⊗ Φ)(ρ) = Φ(Tr_A ρ)`.

Let `Ψ`, `Φ` be channels, `ρ` a density matrix on `A ⊗ B`, and
`(I ⊗ Φ)(ρ) = Σ_j q_j |a_j⟩⟨a_j| ⊗ |b_j⟩⟨b_j|` with unit vectors `|a_j⟩` (the decomposition (18)).
Then the `B`-marginal of the flagged state (19) is `Σ_j q_j |b_j⟩⟨b_j|`, which equals
`Tr_A (I ⊗ Φ)(ρ)`, which equals `Φ(Tr_A ρ)`. In particular `H(σ_B) = H(Φ(Tr_A ρ))`.

**Formalization Note.** `σ_B = traceLeft (traceRight (sigmaABC Ψ q a b))`: first the flag
register, then the `A'` register is traced out. The paper's `Tr_A` traces out the first factor,
so it is `QAlgorithms.traceLeft`. The decomposition (18) is the hypothesis `hdec`; the unit length
of the `|a_j⟩` is the paper's reading of (18) (pure states). -/
theorem eq_22 {A A' B B' : Type*} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A']
    [Fintype B] [DecidableEq B] [Fintype B'] [DecidableEq B']
    (Ψ : Superop A A') (Φ : Superop B B') (hΨ : IsChannel Ψ) (hΦ : IsChannel Φ)
    (ρ : Matrix (A × B) (A × B) ℂ) (hρ : IsDensityMatrix ρ) {m : ℕ} (q : Fin m → ℝ)
    (a : Fin m → EuclideanSpace ℂ A) (ha : ∀ j, ‖a j‖ = 1) (b : Fin m → EuclideanSpace ℂ B')
    (hdec : idTensorSuperop Φ ρ = ∑ j, (q j : ℂ) • (pureDensity (a j) ⊗ₖ pureDensity (b j))) :
    traceLeft (traceRight (sigmaABC Ψ q a b)) = ∑ j, (q j : ℂ) • pureDensity (b j) ∧
      ∑ j, (q j : ℂ) • pureDensity (b j) = traceLeft (idTensorSuperop Φ ρ) ∧
      traceLeft (idTensorSuperop Φ ρ) = Φ (traceLeft ρ) := by sorry

end ShorEBAdditivity
