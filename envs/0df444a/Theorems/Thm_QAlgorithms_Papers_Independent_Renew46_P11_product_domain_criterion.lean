-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P11_product_domain_criterion
-- name    : QAlgorithms.Papers.Independent.Renew46.P11.product_domain_criterion
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T20:07:14.54443+00:00
-- url     : https://prove2.me/theorems/4a3f7ab9-080d-4056-947d-e3210184de67
-- title:
--   Exact product formula characterised by domains
-- statement:
--   Let $(E,F,\Phi)$ be a proper abstract functional calculus on a complex Banach space, with its extension by injective bounded regularisers, and let $f,g\in F_r$. Then
--
--   $$\Phi(f)\Phi(g)=\Phi(fg)\quad\Longleftrightarrow\quad\operatorname{dom}\Phi(fg)\subseteq\operatorname{dom}\Phi(g).$$
--
--   The equality compares full graphs. This criterion distinguishes an exact product formula from equality only after taking the graph closure.
-- source:
--   Product formulas in functional calculi for sectorial operators, arXiv:1309.0318v2, PDF p. 5, Remark 2.2

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

/-- Remark 2.2, PDF p.5: exact equality is characterised by domain inclusion. -/
theorem product_domain_criterion [CompleteSpace X] (C : ElementaryCalculus F X) (hC : IsProper C)
    (f g : F) (hf : Regularisable C f) (hg : Regularisable C g) :
    (graphMul (calculusValue C f) (calculusValue C g) = calculusValue C (f * g)) ↔
      graphDomain (calculusValue C (f * g)) ⊆ graphDomain (calculusValue C g) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P11

end
