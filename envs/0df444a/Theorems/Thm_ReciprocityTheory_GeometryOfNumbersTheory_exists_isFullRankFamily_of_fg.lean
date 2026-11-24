-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_exists_isFullRankFamily_of_fg
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.exists_isFullRankFamily_of_fg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:15:16.72111+00:00
-- url     : https://prove2.me/theorems/39b97aaf-d4b6-48d5-9ab8-0db374ea4e09
-- title:
--   Geometry Of Numbers Theory: exists is Full Rank Family of fg
-- statement:
--   The Geometry Of Numbers Theory construction uses the exists is Full Rank Family of fg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/LatticeCovolumes/DegStA.lean#L22-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/LatticeCovolumes/DegStA.lean#L22-L46

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_ConjSymm
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_DegStA
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
open scoped ComplexOrder Matrix
variable {K : Type*} [Field K] [NumberField K] {V : Type*} [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem ReciprocityTheory.GeometryOfNumbersTheory.exists_isFullRankFamily_of_fg (E : Submodule (𝓞 K) V) (hE : E.FG) :
    ∃ r, ∃ v : Fin r → V, IsFrame K E v := by sorry
