-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ThmIUnique_isMultiHomog_X__5fa82c34cd21
-- name    : P2M_GroundTheory_Heights__Heights_Inter_ThmIUnique_isMultiHomog_X__5fa82c34cd21
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:23:27.897789+00:00
-- url     : https://prove2.me/theorems/658d242a-49f0-4248-bc7a-7a52721301ec
-- title:
--   P2 M Ground Theory Heights  Heights Inter Thm IUnique is Multi Homog X  5fa82c34cd21: P2 M Ground Theory Heights  Heights Inter Thm IUnique is Multi Homog X  5fa82c34cd21
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Thm IUnique is Multi Homog X  5fa82c34cd21 construction uses the P2 M Ground Theory Heights  Heights Inter Thm IUnique is Multi Homog X  5fa82c34cd21 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PThmIUnique.lean#L45-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PThmIUnique.lean#L45-L55

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
open Classical

theorem P2M_GroundTheory_Heights__Heights_Inter_ThmIUnique_isMultiHomog_X__5fa82c34cd21 (k : K) (i : ι k) :
    IsMultiHomog (X ⟨k, i⟩ : MRing ι) (Pi.single k 1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«ThmIUnique».«isMultiHomog_X'» := P2M_GroundTheory_Heights__Heights_Inter_ThmIUnique_isMultiHomog_X__5fa82c34cd21
