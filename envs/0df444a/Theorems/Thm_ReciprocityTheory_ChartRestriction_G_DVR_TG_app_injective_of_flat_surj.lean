-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_TG_app_injective_of_flat_surj
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.TG.app_injective_of_flat_surj
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:07:37.832417+00:00
-- url     : https://prove2.me/theorems/a50a6db4-b22b-4145-8e0c-c5bcf8149968
-- title:
--   TG: app injective of flat surj
-- statement:
--   The TG construction uses the app injective of flat surj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ThetaGenFlat.lean#L149-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ThetaGenFlat.lean#L149-L162

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ThetaGenFlat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.TG
noncomputable section
set_option backward.isDefEq.respectTransparency.types false

theorem ReciprocityTheory.ChartRestriction.G.DVR.TG.app_injective_of_flat_surj {Y Z : Scheme.{0}} (q : Y ⟶ Z) [Flat q] [Surjective q] (V : Z.Opens) :
    Function.Injective (q.app V) := by sorry
