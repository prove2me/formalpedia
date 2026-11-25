-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_discI_of_pos
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.discI_of_pos
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:15:00.796052+00:00
-- url     : https://prove2.me/theorems/7aa5d860-7f57-4998-b3a2-1e0ff9a81fcf
-- title:
--   Geometry Of Numbers Theory: disc I of pos
-- statement:
--   The Geometry Of Numbers Theory construction uses the disc I of pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/PluriharmonicAnalysis/DiscSt.lean#L73-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/PluriharmonicAnalysis/DiscSt.lean#L73-L87

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

theorem ReciprocityTheory.GeometryOfNumbersTheory.discI_of_pos {a R : ℝ} (ha : 0 < a) (hR : 0 ≤ R) :
    discI a R = Real.pi * (1 - Real.exp (-(a * R ^ 2))) / a := by sorry
