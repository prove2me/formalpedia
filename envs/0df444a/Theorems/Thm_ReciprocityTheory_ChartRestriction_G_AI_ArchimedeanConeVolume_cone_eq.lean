-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_ArchimedeanConeVolume_cone_eq
-- name    : ReciprocityTheory.ChartRestriction.G.AI.ArchimedeanConeVolume.cone_eq
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T09:54:26.897227+00:00
-- url     : https://prove2.me/theorems/a68e9ed4-6869-4640-ae1c-f238d8d692b8
-- title:
--   Archimedean Cone Volume: cone eq
-- statement:
--   The Archimedean Cone Volume construction uses the cone eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/LintegralIoiOfRealMul.lean#L208-L226
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/LintegralIoiOfRealMul.lean#L208-L226

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

theorem ReciprocityTheory.ChartRestriction.G.AI.ArchimedeanConeVolume.cone_eq (u : E3) (s : Set ℝ) :
    Ioo (0 : ℝ) 1 • (((↑) : S2 → E3) '' {n : S2 | inner ℝ (n : E3) u ∈ s}) =
      {x : E3 | 0 < ‖x‖ ∧ ‖x‖ < 1 ∧ inner ℝ x u / ‖x‖ ∈ s} := by sorry
