-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ThmIUnique_isMultiHomog_pow__5a8a11fb4ddf
-- name    : P2M_GroundTheory_Heights__Heights_Inter_ThmIUnique_isMultiHomog_pow__5a8a11fb4ddf
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:32:55.512106+00:00
-- url     : https://prove2.me/theorems/15a5e78b-485b-5cbe-acd0-24c843f99c9f
-- title:
--   P2 M Ground Theory Heights  Heights Inter Thm IUnique is Multi Homog pow  5a8a11fb4ddf: P2 M Ground Theory Heights  Heights Inter Thm IUnique is Multi Homog pow  5a8a11fb4ddf
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Thm IUnique is Multi Homog pow  5a8a11fb4ddf construction uses the P2 M Ground Theory Heights  Heights Inter Thm IUnique is Multi Homog pow  5a8a11fb4ddf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PThmIUnique.lean#L57-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PThmIUnique.lean#L57-L63

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedF
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PThmIUnique
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.ThmIUnique
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_ThmIUnique_isMultiHomog_pow__5a8a11fb4ddf {f : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) (n : ℕ) :
    IsMultiHomog (f ^ n) (n • a) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«ThmIUnique».«isMultiHomog_pow'» := P2M_GroundTheory_Heights__Heights_Inter_ThmIUnique_isMultiHomog_pow__5a8a11fb4ddf
