-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_pgds_discI_eq
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.pgds_discI_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:15:34.469275+00:00
-- url     : https://prove2.me/theorems/23790212-9991-4e60-b957-6edc7bad7a36
-- title:
--   Geometry Of Numbers Theory: pgds disc I eq
-- statement:
--   The Geometry Of Numbers Theory construction uses the pgds disc I eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/PluriharmonicAnalysis/DiscSt.lean#L61-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/PluriharmonicAnalysis/DiscSt.lean#L61-L71

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

theorem ReciprocityTheory.GeometryOfNumbersTheory.pgds_discI_eq (a : ℝ) {R : ℝ} (hR : 0 ≤ R) :
    discI a R = ∫ s in (0:ℝ)..R, 2 * Real.pi * (s * Real.exp (-(a * s ^ 2))) := by sorry
