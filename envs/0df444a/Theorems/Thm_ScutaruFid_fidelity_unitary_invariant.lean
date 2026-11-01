-- Prove2me | Theorems.Thm_ScutaruFid_fidelity_unitary_invariant
-- name    : ScutaruFid.fidelity_unitary_invariant
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:58:27.127127+00:00
-- url     : https://prove2.me/theorems/036a3acd-9cdd-444d-9fc4-66cb384b79c6
-- title:
--   Axiom F4: the fidelity is invariant under unitary transformations
-- statement:
--   Let $H$ be a complex Hilbert space, $\rho_1,\rho_2$ density operators on $H$ and $U$ a unitary operator on $H$. Then
--
--   $$
--   F(U\rho_1U^*,\,U\rho_2U^*)=F(\rho_1,\rho_2),
--   $$
--
--   where $F$ is Uhlmann's fidelity (1) with the trace computed in any Hilbert basis. This is axiom F4, which the paper uses to move the first state to a thermal state at the origin.
--
--   Differences from the source:
--   - generalization: unitary transformations on the state space L²(ℝ) → any complex Hilbert space H; reason: the statement on L²(ℝ) is the case H = L²(ℝ)
--   - encoding: states → IsDensityOperator B ρ in a Hilbert basis B, with the same basis for the trace in F; reason: basis-independent trace
-- source:
--   Scutaru, Fidelity for displaced squeezed thermal states and the oscillator semigroup, arXiv:quant-ph/9708013v1, axiom F4 and eq. (1), p.1

import Mathlib
import Definitions.Def_ScutaruFid_IsDensityOperator
import Definitions.Def_ScutaruFid_fidelity

namespace ScutaruFid

/-- **Axiom F4: unitary invariance of the fidelity.** Scutaru, arXiv:quant-ph/9708013v1, axiom F4,
p.1: "F4 F(ρ1, ρ2) is invariant under unitary transformations on the state space. Uhlmann's
transition probability for mixed states [4] F(ρ1, ρ2) = [trace(√ρ1 ρ2 √ρ1)^{1/2}]² (1) does
satisfy F1-F4."

For density operators `ρ, σ` on a complex Hilbert space `H` and a unitary `U` on `H`,
`F(UρU*, UσU*) = F(ρ, σ)`, with `F` Uhlmann's fidelity (1) and the trace taken in any Hilbert
basis.

**Formalization Note** Stated on an arbitrary complex Hilbert space; the paper's state space is
`L²(ℝ)`. -/
theorem fidelity_unitary_invariant {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {ι : Type*} (B : HilbertBasis ι ℂ H) (U : H →L[ℂ] H)
    (hU : U ∈ unitary (H →L[ℂ] H)) (ρ σ : H →L[ℂ] H) (hρ : IsDensityOperator B ρ)
    (hσ : IsDensityOperator B σ) :
    fidelity B (U * ρ * star U) (U * σ * star U) = fidelity B ρ σ := by sorry

end ScutaruFid
