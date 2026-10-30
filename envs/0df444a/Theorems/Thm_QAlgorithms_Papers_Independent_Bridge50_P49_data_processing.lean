-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P49_data_processing
-- name    : QAlgorithms.Papers.Independent.Bridge50.P49.data_processing
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T09:22:26.529103+00:00
-- url     : https://prove2.me/theorems/c5bbaea2-449e-4ae2-978f-0c0155b19173
-- title:
--   Data processing for every sandwiched Rényi order above one
-- statement:
--   Let $\rho,\sigma$ be density matrices on a finite-dimensional Hilbert space, let $\alpha>1$, and let $\Phi$ be any completely positive trace-preserving map to another finite-dimensional matrix space. Let $D_\alpha$ be the natural-log sandwiched divergence, with support inverse powers and value $+\infty$ if the support of its first input is not contained in that of its second. Then
--
--   $$D_\alpha(\Phi(\rho)\|\Phi(\sigma))\leq D_\alpha(\rho\|\sigma).$$
--
--   This is the abstract’s data-processing claim, with arbitrary input and output dimensions and no support-containment premise.
-- source:
--   Sandwiched Rényi Divergence Satisfies Data Processing Inequality, arXiv:1306.5920v6, PDF p. 8, Theorem 6 (Data processing inequality); original page-1 seed

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

/-- Beigi, arXiv:1306.5920v6, Theorem 6, PDF pp.8--9 (abstract p.1).
All finite input/output dimensions and all pairs of states, without a support premise. -/
theorem data_processing {I J : Type} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (a : ℝ) (ha : 1 < a)
    (rho sigma : Mat I) (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (Phi : Superop I J) (hPhi : IsChannel Phi) :
    beigiSandwichedDivergence a (Phi rho) (Phi sigma) ≤ beigiSandwichedDivergence a rho sigma := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P49

end
