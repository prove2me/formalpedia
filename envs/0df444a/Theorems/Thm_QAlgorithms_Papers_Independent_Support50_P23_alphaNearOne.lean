-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P23_alphaNearOne
-- name    : QAlgorithms.Papers.Independent.Support50.P23.alphaNearOne
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T21:01:23.596526+00:00
-- url     : https://prove2.me/theorems/5a8f5d3b-dfc9-4387-9ccc-1769d8fb2b23
-- title:
--   Quantitative approach to order one
-- statement:
--   Let $\rho_{AB}$ and $\sigma_B$ be normalized finite-dimensional states. Define
--   $\eta=\Upsilon(A|B)_{\rho|\sigma}=2^{-H_{3/2}(A|B)_{\rho|\sigma}/2}+2^{H_{1/2}(A|B)_{\rho|\sigma}/2}+1$.
--   On its finite branch, $\eta\ge3$. If $1<\alpha<1+\log_2 3/(4\log_2\eta)$, then
--   $$
--   H_\alpha(A|B)_{\rho|\sigma}\ge H(A|B)_{\rho|\sigma}-4(\alpha-1)(\log_2\eta)^2.
--   $$
--   For $\eta=+\infty$ the displayed order interval is empty. The finite parameter bounds the error when approaching the von Neumann order.
-- source:
--   A Fully Quantum Asymptotic Equipartition Property, arXiv:0811.1221v3, PDF p. 5, Lemma 8: quantitative approach to order one, (25)

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

/-- Lemma 8, PDF p.5, (25). Finite eta is the admissible branch of the printed
interval; eta=infinity leaves no admissible alpha. -/
theorem alphaNearOne [Nonempty A] [Nonempty B]
    (rho : Matrix (A × B) (A × B) ℂ) (sigma : Matrix B B ℂ)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (heta : entropyConvergenceParameter rho sigma ≠ ⊤) (alpha : ℝ) (halpha : 1 < alpha)
    (halphaUpper : alpha < 1 + Real.logb 2 3 / (4 * Real.logb 2 (entropyConvergenceParameter rho sigma).toReal)) :
    fixedVonNeumann rho sigma -
      ((4 * (alpha - 1) * (Real.logb 2 (entropyConvergenceParameter rho sigma).toReal) ^ 2 : ℝ) : EReal) ≤
        finiteAlpha rho sigma alpha := by sorry

end QAlgorithms.Papers.Independent.Support50.P23

end
