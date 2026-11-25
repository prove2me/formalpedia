-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_posDef_norm_dot_sq_le
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.posDef_norm_dot_sq_le
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T10:53:52.446561+00:00
-- url     : https://prove2.me/theorems/8e9842dc-8155-4cf5-ae5a-5fa987295f79
-- title:
--   Geometry Of Numbers Theory: pos Def norm dot sq le
-- statement:
--   The Geometry Of Numbers Theory construction uses the pos Def norm dot sq le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/PluriharmonicAnalysis/BergmanSt.lean#L76-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/PluriharmonicAnalysis/BergmanSt.lean#L76-L97

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_BergmanDefs
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_BergmanSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open MeasureTheory Matrix
open scoped ComplexOrder
variable {X : Type*} [MeasurableSpace X]

theorem ReciprocityTheory.GeometryOfNumbersTheory.posDef_norm_dot_sq_le {r : ℕ} {G : Matrix (Fin r) (Fin r) ℂ} (hG : G.PosDef) (c y : Fin r → ℂ) :
    ‖star y ⬝ᵥ c‖ ^ 2 ≤ (star c ⬝ᵥ G *ᵥ c).re * (star y ⬝ᵥ G⁻¹ *ᵥ y).re := by sorry
