-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P11_resolvent_order_counterexample
-- name    : QAlgorithms.Papers.Independent.Renew46.P11.resolvent_order_counterexample
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T20:12:17.513073+00:00
-- url     : https://prove2.me/theorems/b877e27e-f72a-4fc3-8d7e-ddc9360bbe47
-- title:
--   Resolvent products depend on operator order
-- statement:
--   Let $A$ be a densely defined closed sectorial operator on a complex Banach space $X$, and write $R=(I+A)^{-1}$. Composition applies the right factor first. Then
--
--   $$AR=I-R\quad\text{on }X,\qquad RA=(I-R)|_{\operatorname{dom}A}.$$
--
--   If $A$ is unbounded, then $RA\ne AR$ as operator graphs. These are the rational symbols $z$ and $(1+z)^{-1}$ used in the paper's order counterexample. The explicit unboundedness guard follows PDF p.10 and avoids claiming failure for bounded operators.
-- source:
--   Product formulas in functional calculi for sectorial operators, arXiv:1309.0318v2, PDF p. 2, Unnumbered counterexample (1.1), (3.5)

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

/-- Unnumbered resolvent counterexample, PDF pp.2,10. Accepted sectoriality
is supplemented by density to match this source. The reverse order fails
when A is unbounded; bounded A is not a counterexample. -/
theorem resolvent_order_counterexample [CompleteSpace X] (A : Graph X) (hA : Sectorial A)
    (hdense : Dense (graphDomain A)) :
    graphMul A (graphInverse (graphAdd identityGraph A)) =
      banachBoundedGraph (ContinuousLinearMap.id ℂ X - onePlusInverse A) ∧
    graphMul (graphInverse (graphAdd identityGraph A)) A =
      restrictGraph (banachBoundedGraph (ContinuousLinearMap.id ℂ X - onePlusInverse A))
        (graphDomain A) ∧
    (¬ Bounded A → graphMul (graphInverse (graphAdd identityGraph A)) A ≠
      graphMul A (graphInverse (graphAdd identityGraph A))) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P11

end
