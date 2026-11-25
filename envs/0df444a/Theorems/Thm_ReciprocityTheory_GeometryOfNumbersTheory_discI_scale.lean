-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_discI_scale
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.discI_scale
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:53:28.546086+00:00
-- url     : https://prove2.me/theorems/63dabad9-9e41-4977-9a4b-cc78dda0c314
-- title:
--   Geometry Of Numbers Theory: disc I scale
-- statement:
--   The Geometry Of Numbers Theory construction uses the disc I scale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/PluriharmonicAnalysis/DiscSt.lean#L104-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/PluriharmonicAnalysis/DiscSt.lean#L104-L114

import Mathlib
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_DiscSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open MeasureTheory Filter Topology
open Set

theorem ReciprocityTheory.GeometryOfNumbersTheory.discI_scale {a R t : ℝ} (ha : 0 ≤ a) (hR : 0 ≤ R) (ht : 0 < t) :
    discI (t * a) (R / Real.sqrt t) = discI a R / t := by sorry
