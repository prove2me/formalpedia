-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_supSt_adt_eq
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.supSt_adt_eq
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T10:53:59.38946+00:00
-- url     : https://prove2.me/theorems/4868de30-7199-5a20-9eb2-3d6f34249b2f
-- title:
--   Geometry Of Numbers Theory: sup St adt eq
-- statement:
--   The Geometry Of Numbers Theory construction uses the sup St adt eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/SphericalMonomials/SupStMonoNormSqPos.lean#L8-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/SphericalMonomials/SupStMonoNormSqPos.lean#L8-L11

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

theorem ReciprocityTheory.GeometryOfNumbersTheory.supSt_adt_eq (D n : ℕ) :
    Finset.Nat.antidiagonalTuple (D + 1) n = Finset.piAntidiag Finset.univ n := by sorry
