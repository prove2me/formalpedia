-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_supSt_gram
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.supSt_gram
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T10:54:30.276843+00:00
-- url     : https://prove2.me/theorems/ac9bdaaf-7522-4d2c-8793-fc71266818d5
-- title:
--   Geometry Of Numbers Theory: sup St gram
-- statement:
--   The Geometry Of Numbers Theory construction uses the sup St gram property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/SphericalMonomials/SupStMonoNormSqPos.lean#L66-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/SphericalMonomials/SupStMonoNormSqPos.lean#L66-L78

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_MonomSt
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_BergmanDefs
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_SupStMonoNormSqPos
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open MeasureTheory

theorem ReciprocityTheory.GeometryOfNumbersTheory.supSt_gram {D : ℕ} (a b : Fin (D + 1) → ℕ) :
    ∫ z, starRingEnd ℂ (monoC a z) * monoC b z ∂(sphProb (D + 1)) =
      if a = b then (monoNormSq a : ℂ) else 0 := by sorry
