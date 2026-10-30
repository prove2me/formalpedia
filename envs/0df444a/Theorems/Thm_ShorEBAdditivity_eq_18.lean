-- Prove2me | Theorems.Thm_ShorEBAdditivity_eq_18
-- name    : ShorEBAdditivity.eq_18
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T03:18:49.997417+00:00
-- url     : https://prove2.me/theorems/c8efaec4-0d21-4022-bab7-4ed75aec9a8a
-- title:
--   Eq. (18): $(I\otimes\Phi)(\rho) = \sum_j q_j |a_j\rangle\langle a_j|\otimes|b_j\rangle\langle b_j|$ for entanglement-breaking $\Phi$
-- statement:
--   Let $\Phi : M_B \to M_{B'}$ be a quantum channel (a completely positive trace-preserving map) that is entanglement breaking, and let $\rho$ be a density matrix on $\mathcal H_A\otimes\mathcal H_B$. Then there are finitely many weights $q_j \ge 0$ with $\sum_j q_j = 1$, unit vectors $|a_j\rangle \in \mathcal H_A$ and unit vectors $|b_j\rangle \in \mathcal H_{B'}$ such that
--
--   $$
--   (I\otimes\Phi)(\rho) = \sum_j q_j\, |a_j\rangle\langle a_j| \otimes |b_j\rangle\langle b_j| .
--   $$
--
--   This is the decomposition on which the whole proof of additivity rests: it turns the output of $I\otimes\Phi$ into a mixture of product pure states, so that a classical flag can be attached to it.
--
--   **Formalization Note** $I\otimes\Phi$ is `QAlgorithms.idTensorSuperop Φ`, with the identity on the first factor $A$; $|a\rangle\langle a|$ is `QAlgorithms.pureDensity a`. Channels are `QAlgorithms.IsChannel` (a finite normalized Kraus family).
--
--   Differences from the source:
--   - reading: "for some qij, |aij⟩, |bij⟩" → q_j ≥ 0 with Σ_j q_j = 1 and unit vectors a_j, b_j; reason: the display writes projectors onto pure states, and the same decomposition in Theorem 1 is used with "Since Σ_j q_j = 1" (p.3)
--   - generalization: ρ_i a signal state of the optimal ensemble (17) → any density matrix ρ on A × B; reason: (18) uses only that ρ_i is a state, and every signal state is one
--   - encoding: quantum channel (CPTP map) → IsChannel Φ (finite normalized Kraus family); reason: in finite dimension the CPTP maps are exactly the maps with a finite Kraus representation (Choi–Kraus); same maps
--   - encoding: another quantum system Href in the definition of entanglement breaking → every reference ℂ^a (Fin a), a ∈ ℕ; reason: every finite-dimensional system is isomorphic to some ℂ^a
-- source:
--   Shor, Additivity of the Classical Capacity of Entanglement-Breaking Quantum Channels, arXiv:quant-ph/0201149v3, eq. (18), p.4 (and eq. (7), p.2)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_ShorEBAdditivity_IsEntanglementBreaking

open QAlgorithms
open scoped Kronecker

namespace ShorEBAdditivity

/-- Shor, *Additivity of the Classical Capacity of Entanglement-Breaking Quantum Channels*,
arXiv:quant-ph/0201149v3, eq. (18), p.4 (and eq. (7), p.2): "Let us consider the state
(I ⊗ Φ)(ρi). Because Φ is an entanglement breaking map, this state is separable, and so
(I ⊗ Φ)(ρi) = Σ_j qij |aij⟩⟨aij| ⊗ |bij⟩⟨bij| for some qij, |aij⟩, |bij⟩."

For a channel `Φ : M_B → M_{B'}` that is entanglement breaking and a density matrix `ρ` on
`A ⊗ B`, there are finitely many probability weights `q_j`, unit vectors `|a_j⟩ ∈ ℂ^A` and unit
vectors `|b_j⟩ ∈ ℂ^{B'}` with `(I ⊗ Φ)(ρ) = Σ_j q_j |a_j⟩⟨a_j| ⊗ |b_j⟩⟨b_j|`.

**Formalization Note.** `I ⊗ Φ` is `QAlgorithms.idTensorSuperop Φ`, with the identity on the
first factor `A`. `|a⟩⟨a|` is `QAlgorithms.pureDensity a`. The weights are a probability
distribution and the vectors are unit vectors: this is the paper's reading of the display
(projectors onto pure states, and "Since Σ_j q_j = 1", p.3). `IsEntanglementBreaking` quantifies
over references `Fin a`; here the reference is an arbitrary finite type `A`. -/
theorem eq_18 {A B B' : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype B'] [DecidableEq B'] (Φ : Superop B B') (hΦ : IsChannel Φ)
    (hEB : IsEntanglementBreaking Φ) (ρ : Matrix (A × B) (A × B) ℂ) (hρ : IsDensityMatrix ρ) :
    ∃ (m : ℕ) (q : Fin m → ℝ) (a : Fin m → EuclideanSpace ℂ A)
      (b : Fin m → EuclideanSpace ℂ B'),
      (∀ j, 0 ≤ q j) ∧ ∑ j, q j = 1 ∧ (∀ j, ‖a j‖ = 1) ∧ (∀ j, ‖b j‖ = 1) ∧
      idTensorSuperop Φ ρ = ∑ j, (q j : ℂ) • (pureDensity (a j) ⊗ₖ pureDensity (b j)) := by sorry

end ShorEBAdditivity
