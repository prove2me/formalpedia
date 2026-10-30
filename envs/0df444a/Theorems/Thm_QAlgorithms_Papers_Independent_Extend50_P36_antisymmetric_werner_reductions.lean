-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P36_antisymmetric_werner_reductions
-- name    : QAlgorithms.Papers.Independent.Extend50.P36.antisymmetric_werner_reductions
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T14:04:08.877107+00:00
-- url     : https://prove2.me/theorems/c8382670-df38-415b-8719-a92e2f5730c6
-- title:
--   Sec. III A, unnumbered: antisymmetric state gives the extremal Werner marginal
-- statement:
--   Let $d\ge2$ be an integer. Write $\rho_W(\psi)$ for the $d$-dimensional Werner state with swap expectation $\psi\in[-1,1]$, and $\rho_I(\phi)$ for the isotropic state with $\phi=dF\in[0,d]$, where $F$ is its overlap with the normalized maximally entangled vector. A joining state is a positive semidefinite operator of trace one having the specified ordered pair marginals.
--
--   For $d\ge2$, let $v_d=(d!)^{-1/2}\sum_{\pi\in S_d}\operatorname{sgn}(\pi)V_\pi|0,1,\ldots,d-1\rangle$. This vector is normalized, and every ordered pair of distinct sites $i,j$ satisfies
--   $$\operatorname{Tr}_{\widehat{ij}}|v_d\rangle\langle v_d|=\rho_W(-1).$$
--   Thus the extremal Werner state is a two-party reduction of the fully antisymmetric pure state.
-- source:
--   Compatible quantum correlations: on extension problems for Werner and isotropic states, arXiv:1305.1342v3, PDF p. 6, Sec. III A, unnumbered: antisymmetric state gives the extremal Werner marginal

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P36

noncomputable section

open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P36

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact accepted matrix alias; tensor reductions below compose frozen superoperators.

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

/-- Sec.III A, Eq.(7), PDF pp.6–7: every distinct pair of the normalized fully
antisymmetric d-party pure state is the extremal Werner state. -/
theorem antisymmetric_werner_reductions (d : ℕ) (hd : 2 ≤ d) :
    ‖fullAntisymmetricVector d‖ = 1 ∧
    ∀ i j : Fin d, i ≠ j → pairMarginal (pureDensity (fullAntisymmetricVector d)) i j = wernerSwapState d (-1) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P36

end
