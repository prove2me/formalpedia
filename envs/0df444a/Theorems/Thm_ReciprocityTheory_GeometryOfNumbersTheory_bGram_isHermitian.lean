-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_bGram_isHermitian
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.bGram_isHermitian
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:52:19.486815+00:00
-- url     : https://prove2.me/theorems/6d466644-6392-5438-bdb8-6621f05adf2a
-- title:
--   Geometry Of Numbers Theory: b Gram is Hermitian
-- statement:
--   The Geometry Of Numbers Theory construction uses the b Gram is Hermitian property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/PluriharmonicAnalysis/BergmanDerivSt.lean#L14-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/PluriharmonicAnalysis/BergmanDerivSt.lean#L14-L21

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_BergmanSt
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_LogDetSt
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_BergmanDerivSt
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

theorem ReciprocityTheory.GeometryOfNumbersTheory.bGram_isHermitian (μ : Measure X) {r : ℕ} (s : Fin r → X → ℂ) (w : X → ℝ) :
    (bGram μ s w).IsHermitian := by sorry
