-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_supSt_integrable
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.supSt_integrable
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T10:54:52.857262+00:00
-- url     : https://prove2.me/theorems/403e1eb3-7c16-4ff0-8945-fdf2b95edde6
-- title:
--   Geometry Of Numbers Theory: sup St integrable
-- statement:
--   The Geometry Of Numbers Theory construction uses the sup St integrable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/SphericalMonomials/SupStMonoNormSqPos.lean#L56-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/SphericalMonomials/SupStMonoNormSqPos.lean#L56-L64

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

theorem ReciprocityTheory.GeometryOfNumbersTheory.supSt_integrable {D : ℕ} (a b : Fin (D + 1) → ℕ) :
    Integrable (fun z => starRingEnd ℂ (monoC a z) * monoC b z) (sphProb (D + 1)) := by sorry
