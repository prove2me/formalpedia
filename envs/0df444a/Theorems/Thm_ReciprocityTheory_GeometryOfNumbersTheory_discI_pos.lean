-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_discI_pos
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.discI_pos
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:52:43.708171+00:00
-- url     : https://prove2.me/theorems/4ae4b5de-823d-51c1-a386-c9e1507b5e86
-- title:
--   Geometry Of Numbers Theory: disc I pos
-- statement:
--   The Geometry Of Numbers Theory construction uses the disc I pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/PluriharmonicAnalysis/DiscSt.lean#L95-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/PluriharmonicAnalysis/DiscSt.lean#L95-L102

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

theorem ReciprocityTheory.GeometryOfNumbersTheory.discI_pos {a R : ℝ} (ha : 0 ≤ a) (hR : 0 < R) : 0 < discI a R := by sorry
