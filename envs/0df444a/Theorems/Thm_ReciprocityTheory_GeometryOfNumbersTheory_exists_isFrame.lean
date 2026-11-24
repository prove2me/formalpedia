-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_exists_isFrame
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.exists_isFrame
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T20:23:09.677723+00:00
-- url     : https://prove2.me/theorems/3f713b87-f96f-4805-afe6-4e027e38e31e
-- title:
--   Geometry Of Numbers Theory: exists is Frame
-- statement:
--   The Geometry Of Numbers Theory construction uses the exists is Frame property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/LatticeCovolumes/ArakelovDegreeEqDegreeOfFamily.lean#L11-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/LatticeCovolumes/ArakelovDegreeEqDegreeOfFamily.lean#L11-L15

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_DegStB
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_ArakelovDegreeEqDegreeOfFamily
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open NumberField Module
open scoped ComplexOrder
variable {K : Type*} [Field K] [NumberField K] {V : Type*} [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem ReciprocityTheory.GeometryOfNumbersTheory.exists_isFrame (E : Submodule (𝓞 K) V) (hE : E.FG) :
    ∃ v : Fin (latRank K E) → V, IsFrame K E v := by sorry
