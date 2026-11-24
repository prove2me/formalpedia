-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_powLog_nonneg
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.powLog_nonneg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:15:09.382803+00:00
-- url     : https://prove2.me/theorems/15af7605-b979-4a52-a54a-0448c9a44047
-- title:
--   Geometry Of Numbers Theory: pow Log nonneg
-- statement:
--   The Geometry Of Numbers Theory construction uses the pow Log nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/AsymptoticSequences/DefectSt.lean#L62-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/AsymptoticSequences/DefectSt.lean#L62-L64

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_ChiPSt
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_AsymptoticSequences_DefectSt
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
open Filter Topology Asymptotics

theorem ReciprocityTheory.GeometryOfNumbersTheory.powLog_nonneg (D n : ℕ) : 0 ≤ (n : ℝ) ^ D * Real.log ((n : ℝ) + 1) := by sorry
