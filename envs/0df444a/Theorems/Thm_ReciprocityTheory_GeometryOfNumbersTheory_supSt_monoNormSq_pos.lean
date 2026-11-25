-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_supSt_monoNormSq_pos
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.supSt_monoNormSq_pos
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T10:54:28.053795+00:00
-- url     : https://prove2.me/theorems/49a501e6-6aac-41b2-aad7-448e270e7fde
-- title:
--   Geometry Of Numbers Theory: sup St mono Norm Sq pos
-- statement:
--   The Geometry Of Numbers Theory construction uses the sup St mono Norm Sq pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/SphericalMonomials/SupStMonoNormSqPos.lean#L110-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/SphericalMonomials/SupStMonoNormSqPos.lean#L110-L114

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

theorem ReciprocityTheory.GeometryOfNumbersTheory.supSt_monoNormSq_pos {D : ℕ} (a : Fin (D + 1) → ℕ) : 0 < monoNormSq a := by sorry
