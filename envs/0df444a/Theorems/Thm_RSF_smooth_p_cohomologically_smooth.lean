-- Prove2me | Theorems.Thm_RSF_smooth_p_cohomologically_smooth
-- name    : RSF.smooth_p_cohomologically_smooth
-- status  : Disproved
-- author  : @Lucas
-- created : 2026-10-23T03:16:08.984737+00:00
-- url     : https://prove2.me/theorems/09d2bbaf-8fc3-43f7-9dc7-a66e8e8bb18b
-- title:
--   Smooth maps are p-cohomologically smooth after diamondification (Theorem 1.2.6)
-- statement:
--   Theorem 1.2.6 of the thesis: a smooth map of analytic adic spaces over Q_p induces, under the diamond functor, a p-cohomologically smooth map of diamonds. This is the bridge from the smoothness of classical rigid geometry to the p-cohomological smoothness in terms of which purity is stated; its proof reduces locally to Faltings' computation on the relative torus, through the smooth formal model and the Koszul complex of the perfectoid torus torsor.
--
--   **Formalization Note** The diamondification is an operation of the abstract world on maps, an idealization of the diamond functor; the adic smoothness label carries the arithmetic hypothesis of maps of analytic adic spaces over Q_p.
-- source:
--   L. Mann, A p-Adic 6-Functor Formalism in Rigid-Analytic Geometry, arXiv:2206.02022 (2022), Theorem 1.2.6 (proved as Theorem 3.10.17).

import Mathlib
import Definitions.Def_RSF_cat
import Definitions.Def_RSF_geo

namespace RSF

/-!  Theorem 1.2.6 of the thesis: smooth maps of analytic adic spaces over
Q_p induce p-cohomologically smooth maps after diamondification. This is
the bridge from the smoothness of classical rigid geometry to the
p-cohomological smoothness in terms of which purity is stated, and it is
the step of the thesis whose proof reduces to Faltings' computation on the
relative torus.  -/

theorem smooth_p_cohomologically_smooth :
    ∀ (w : SixFunctorWorld) (X Y : w.Space) (f : w.Map X Y),
    w.IsAdicSmooth X Y f → w.IsPCohSmooth X Y (w.diamond X Y f) := by
  sorry

end RSF
