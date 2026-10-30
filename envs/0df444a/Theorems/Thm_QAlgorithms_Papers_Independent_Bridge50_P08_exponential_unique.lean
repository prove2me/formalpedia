-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P08_exponential_unique
-- name    : QAlgorithms.Papers.Independent.Bridge50.P08.exponential_unique
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T12:18:11.221633+00:00
-- url     : https://prove2.me/theorems/d95204a9-7426-4b04-abcc-efb6f5ff1ec9
-- title:
--   Uniqueness of the ODE exponential function
-- statement:
--   Let $G$ be a Hausdorff Lie group modelled on an arbitrary Hausdorff locally convex real space, in the jointly continuous directional calculus. If $E_1,E_2:T_1G\to G$ are smooth exponential functions in the sense that, for every $x\in T_1G$, their values are the time-one endpoints of global smooth curves solving $\gamma(0)=1$ and $\gamma^{\prime}(t)=T_1\lambda_{\gamma(t)}(x)$, where $\lambda_g$ denotes left multiplication by $g$, then
--
--   $$E_1=E_2.$$
--
--   Thus an exponential function, when it exists, is determined by the given Lie group structure. Existence and local invertibility are not conclusions.
-- source:
--   Principal 2-bundles and their gauge 2-groups, arXiv:0803.3692v4, PDF p. 36, Remark A.5: uniqueness of an exponential function

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P08

namespace QAlgorithms.Papers.Independent.Bridge50.P08

open Set Filter Topology

open QAlgorithms.Papers.Independent.Renew46.P18

open QAlgorithms.Papers.Independent.Claimed50.P22

open QAlgorithms.Papers.Independent.Next46.P35

universe u v w z

attribute [local instance] QAlgorithms.Papers.Independent.Bridge50.P08.productCharts

/-- Remark A.5, PDF p. 36: a Hausdorff locally convex Lie group has at
most one smooth exponential function in the ODE sense of A.3. Existence
is not asserted and neither local exponentiality nor regularity is assumed. -/
theorem exponential_unique
    {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [LocallyConvexSpace ℝ E] [T2Space E]
    {G : Type v} [Group G] [TopologicalSpace G] [T2Space G] [ChartedSpace E G]
    (hG : IsDirectionalLieGroup (E := E) (G := G))
    (expOne expTwo : E → G)
    (hOne : IsExponentialFunction expOne)
    (hTwo : IsExponentialFunction expTwo) : expOne = expTwo := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P08
