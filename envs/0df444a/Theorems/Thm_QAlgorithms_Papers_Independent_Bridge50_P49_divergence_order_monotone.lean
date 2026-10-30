-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P49_divergence_order_monotone
-- name    : QAlgorithms.Papers.Independent.Bridge50.P49.divergence_order_monotone
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T09:23:15.794851+00:00
-- url     : https://prove2.me/theorems/1a9e246b-eff7-4a76-b551-e69789303520
-- title:
--   Monotonicity of sandwiched Rényi divergence in the order
-- statement:
--   For any two density matrices $\rho,\sigma$ on a finite-dimensional Hilbert space, let $D_\alpha$ denote the natural-log sandwiched Rényi divergence, with value $+\infty$ on support failure. Its dependence on the order is nondecreasing above one: for all real $1<\alpha\leq\beta$,
--
--   $$D_\alpha(\rho\|\sigma)\leq D_\beta(\rho\|\sigma).$$
--
--   Nondecreasing is the meaning of “increasing” used here; identical states give zero at every order.
-- source:
--   Sandwiched Rényi Divergence Satisfies Data Processing Inequality, arXiv:1306.5920v6, PDF p. 9, Theorem 7 (Monotonicity in α)

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P49

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder ENNReal

open Filter Topology

namespace QAlgorithms.Papers.Independent.Bridge50.P49

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Information100.P50 (schattenNorm)

open QAlgorithms.Papers.Independent.Information100.P58 (Distribution)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P62 (tensorChannel)

open QAlgorithms.Papers.Independent.Dependency50.P35
  (spectralPower Dominates rawTrace leftMarginal rightMarginal marginalAB marginalAC)

/-- Beigi, arXiv:1306.5920v6, Theorem 7, PDF p.9: increasing means nondecreasing. -/
theorem divergence_order_monotone {I : Type} [Fintype I] [DecidableEq I]
    (rho sigma : Mat I) (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma) :
    MonotoneOn (fun a : ℝ => beigiSandwichedDivergence a rho sigma) (Set.Ioi 1) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P49

end
