-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P23_alphaMonotone
-- name    : QAlgorithms.Papers.Independent.Support50.P23.alphaMonotone
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T20:57:33.444691+00:00
-- url     : https://prove2.me/theorems/68c23c51-56a9-40ef-8181-7bcab46f5ca7
-- title:
--   Monotonicity of fixed-reference Petz conditional entropies
-- statement:
--   Let $\rho_{AB}$ and $\sigma_B$ be normalized states on finite-dimensional nonzero complex systems. For finite $\alpha>0$, $\alpha\ne1$, use the regularized Petz conditional entropy $H_\alpha=(1-\alpha)^{-1}\log_2\operatorname{tr}[\rho_{AB}^{\alpha}(I_A\otimes\sigma_B)^{1-\alpha}]$. Order one is the fixed-reference von Neumann entropy; zero and infinity are its order limits. For every $0\le\alpha\le\beta\le\infty$,
--   $$
--   H_\beta(A|B)_{\rho|\sigma}\le H_\alpha(A|B)_{\rho|\sigma}.
--   $$
--   Singular references retain extended values. The reference is fixed throughout; this result compares orders within the same family.
-- source:
--   A Fully Quantum Asymptotic Equipartition Property, arXiv:0811.1221v3, PDF p. 4, Lemma 3: monotonicity of fixed-reference alpha entropy

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P23

noncomputable section

open Filter

open scoped ENNReal ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Support50.P23

attribute [local instance] Classical.propDecidable

-- Exact accepted bodies. Other similarly named catalogue entries use different
-- smoothing, conditioning order, logarithm base, or channel-level objects.

open QAlgorithms.Papers.Independent.Gap20.P03 (fixedMin)

open QAlgorithms.Papers.Independent.Dependency50.P36 (relativeEntropy)

open QAlgorithms.Papers.Independent.Information100.P67 (IsSubnormalized)

open QAlgorithms.Papers.Independent.Information100.P69 (matrixPower)

variable {A B C D I : Type*}

variable [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype I]

variable [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D] [DecidableEq I]

/-- Lemma 3, PDF p.4: decreasing fixed-reference entropy at all orders, including 0,1,infinity. -/
theorem alphaMonotone [Nonempty A] [Nonempty B]
    (rho : Matrix (A × B) (A × B) ℂ) (sigma : Matrix B B ℂ)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma) :
    Antitone (alphaEntropy rho sigma) := by sorry

end QAlgorithms.Papers.Independent.Support50.P23

end
