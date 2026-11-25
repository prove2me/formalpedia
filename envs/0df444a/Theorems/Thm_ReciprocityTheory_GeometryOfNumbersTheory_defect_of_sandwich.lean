-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_defect_of_sandwich
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.defect_of_sandwich
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T14:27:10.062735+00:00
-- url     : https://prove2.me/theorems/0782f55b-2dcd-51c2-ba18-d48cb33c8529
-- title:
--   Geometry Of Numbers Theory: defect of sandwich
-- statement:
--   The Geometry Of Numbers Theory construction uses the defect of sandwich property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/AsymptoticSequences/DefectSt.lean#L124-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/AsymptoticSequences/DefectSt.lean#L124-L176

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

theorem ReciprocityTheory.GeometryOfNumbersTheory.defect_of_sandwich (D k : ℕ) (δ hh C : ℝ) (hδ : 0 ≤ δ) (chi : ℕ → ℝ)
    (hlo : ∀ n : ℕ, k + 1 ≤ n → δ * chiP D (n - k) - C * (n : ℝ) ^ D * Real.log (n + 1) ≤ chi n)
    (hhi : ∀ n : ℕ, 1 ≤ n → chi n ≤ δ * chiP D (n + k) + C * (n : ℝ) ^ D * Real.log (n + 1)) :
    (fun n => hsDefect D chi (δ * hh) n - δ * hsDefect D (chiP D) hh n) =o[atTop]
      fun n : ℕ => (n : ℝ) ^ (D + 1) := by sorry
