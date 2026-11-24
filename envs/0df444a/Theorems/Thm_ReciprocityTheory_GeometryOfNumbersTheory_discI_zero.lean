-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_discI_zero
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.discI_zero
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:15:12.575802+00:00
-- url     : https://prove2.me/theorems/d2c3023f-9a52-4c12-a448-26e329b69f64
-- title:
--   Geometry Of Numbers Theory: disc I zero
-- statement:
--   The Geometry Of Numbers Theory construction uses the disc I zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/PluriharmonicAnalysis/DiscSt.lean#L89-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/PluriharmonicAnalysis/DiscSt.lean#L89-L93

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

theorem ReciprocityTheory.GeometryOfNumbersTheory.discI_zero {R : ℝ} (hR : 0 ≤ R) : discI 0 R = Real.pi * R ^ 2 := by sorry
