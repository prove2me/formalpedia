-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P36_separable_werner_triple_obstruction
-- name    : QAlgorithms.Papers.Independent.Extend50.P36.separable_werner_triple_obstruction
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T14:06:41.411575+00:00
-- url     : https://prove2.me/theorems/85000dde-76e4-4739-9ac4-ed29fe49403c
-- title:
--   Sec. III C, unnumbered: separable Werner triple with no extension
-- statement:
--   Let $d\ge2$ be an integer. Write $\rho_W(\psi)$ for the $d$-dimensional Werner state with swap expectation $\psi\in[-1,1]$, and $\rho_I(\phi)$ for the isotropic state with $\phi=dF\in[0,d]$, where $F$ is its overlap with the normalized maximally entangled vector. A joining state is a positive semidefinite operator of trace one having the specified ordered pair marginals.
--
--   For every $d\ge2$, both $\rho_W(1)$ and $\rho_W(0)$ are separable. Nevertheless,
--   $$\rho_{AB}=\rho_W(1),\quad \rho_{AC}=\rho_W(1),\quad \rho_{BC}=\rho_W(0)\quad\text{have no common joining density operator}.$$
--   Thus pairwise separability does not suffice for three-pair compatibility.
-- source:
--   Compatible quantum correlations: on extension problems for Werner and isotropic states, arXiv:1305.1342v3, PDF p. 9, Sec. III C, unnumbered: separable Werner triple with no extension

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P36

noncomputable section

open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P36

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact accepted matrix alias; tensor reductions below compose frozen superoperators.

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

/-- Sec.III C, PDF p.9: the explicit triple (AB,AC,BC)=(1,1,0) is separable
pairwise but incompatible, for every d>=2. -/
theorem separable_werner_triple_obstruction (d : ℕ) (hd : 2 ≤ d) :
    (letI : Nonempty (Fin d) := ⟨⟨0,by omega⟩⟩
     Entanglement.IsSeparableDensity (wernerSwapState d 1) ∧
     Entanglement.IsSeparableDensity (wernerSwapState d 0)) ∧
    ¬ JoinableThree (wernerSwapState d 1) (wernerSwapState d 1) (wernerSwapState d 0) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P36

end
