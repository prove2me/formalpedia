-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P11_bernstein_geometric_product_failure
-- name    : QAlgorithms.Papers.Independent.Renew46.P11.bernstein_geometric_product_failure
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T20:11:40.153215+00:00
-- url     : https://prove2.me/theorems/83506766-87f6-46e0-93aa-620dd6328e1c
-- title:
--   No positive exponents restore Bernstein closure
-- statement:
--   For arbitrary real exponents $\alpha>0$ and $\beta>0$, define $F(x)=(1-e^{-x})^\alpha x^\beta$ for $x>0$, using positive real powers. Then
--
--   $$F\notin\mathrm{BF}.$$
--
--   Here $\mathrm{BF}$ is the class of nonnegative smooth functions whose derivative is completely monotone on $(0,\infty)$. Thus the two displayed Bernstein functions fail the proposed positive-power closure for every positive exponent pair; no derivative inequality is assumed.
-- source:
--   Product formulas in functional calculi for sectorial operators, arXiv:1309.0318v2, PDF p. 30, Example 5.7

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P11

noncomputable section

attribute [local instance] Classical.propDecidable

open Set Filter MeasureTheory

open scoped Topology ContDiff NNReal

namespace QAlgorithms.Papers.Independent.Renew46.P11

open QAlgorithms.Papers.Independent.Next46.P06

open QAlgorithms.Papers.Independent.Claimed50.P05 (graphDomain GraphCore restrictGraph)

universe u v w

variable {F : Type u} [CommRing F] [Algebra ℂ F]

variable {X : Type v} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

variable {Y : Type w} [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]

/-- Example 5.7, PDF p.30: no positive pair of exponents makes the displayed
product a Bernstein function; the derivative bound is not assumed. -/
theorem bernstein_geometric_product_failure (alpha beta : ℝ)
    (ha : 0 < alpha) (hb : 0 < beta) :
    ¬ Bernstein (fun x : ℝ => Real.rpow (1 - Real.exp (-x)) alpha *
      Real.rpow x beta) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P11

end
