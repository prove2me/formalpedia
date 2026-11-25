-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_ArchimedeanConeVolume_toSphere_univ_ne_top
-- name    : ReciprocityTheory.ChartRestriction.G.AI.ArchimedeanConeVolume.toSphere_univ_ne_top
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T09:54:31.244802+00:00
-- url     : https://prove2.me/theorems/eb0f2b6a-bcfc-4907-9903-1f8380fc7e0c
-- title:
--   Archimedean Cone Volume: to Sphere univ ne top
-- statement:
--   The Archimedean Cone Volume construction uses the to Sphere univ ne top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/LintegralIoiOfRealMul.lean#L231-L232
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/LintegralIoiOfRealMul.lean#L231-L232

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_KappaA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LintegralIoiOfRealMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set Real
open scoped ENNReal Pointwise
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.ArchimedeanConeVolume

theorem ReciprocityTheory.ChartRestriction.G.AI.ArchimedeanConeVolume.toSphere_univ_ne_top : (volume : Measure E3).toSphere univ ≠ ⊤ := by sorry
