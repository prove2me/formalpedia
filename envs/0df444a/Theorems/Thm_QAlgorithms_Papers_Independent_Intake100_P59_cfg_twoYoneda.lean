-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P59_cfg_twoYoneda
-- name    : QAlgorithms.Papers.Independent.Intake100.P59.cfg_twoYoneda
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:05:57.995466+00:00
-- url     : https://prove2.me/theorems/b2656296-ef42-4e4b-b651-f4319b499013
-- title:
--   2-Yoneda via evaluation at the identity
-- statement:
--   Let $p:D\to C$ be any category fibered in groupoids and $X$ any object of $C$. The representable CFG $\underline X$ is the slice $C/X$ with its domain projection. In $\operatorname{Hom}_{\mathrm{CFG}}(\underline X,D)$, objects are functors strictly over $C$ and arrows are natural transformations whose components project to base identities. Evaluation at the identity is an equivalence of categories:
--
--   $$
--   \Theta:\operatorname{Hom}_{\mathrm{CFG}}(\underline X,D)\longrightarrow D(X),\qquad F\longmapsto F(\mathrm{id}_X),\qquad\alpha\longmapsto\alpha_{\mathrm{id}_X}.
--   $$
--
--   In particular this specific functor is fully faithful and essentially surjective. No descent hypothesis on $D$ is needed. This describes maps from representable CFGs intrinsically.
-- source:
--   Orbifolds as stacks?, arXiv:0806.4160v2, PDF p. 23, Lemma 4.19

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P59

namespace QAlgorithms.Papers.Independent.Intake100.P59

open CategoryTheory

universe u v uC vC uD vD uE vE

/-- Lemma 4.19 (2-Yoneda), PDF pp.23–24: the specified evaluation functor is
fully faithful and essentially surjective for any CFG. No descent or stack
hypothesis is required. Natural transformations in its domain are vertical. -/
theorem cfg_twoYoneda
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    (p : D ⥤ C) (hp : IsCFG p) (X : C) :
    (yonedaEvaluation p X).IsEquivalence := by sorry

end QAlgorithms.Papers.Independent.Intake100.P59
