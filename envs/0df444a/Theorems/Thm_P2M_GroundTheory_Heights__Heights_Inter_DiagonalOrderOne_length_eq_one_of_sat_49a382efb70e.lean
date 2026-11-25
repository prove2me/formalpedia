-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagonalOrderOne_length_eq_one_of_sat_49a382efb70e
-- name    : P2M_GroundTheory_Heights__Heights_Inter_DiagonalOrderOne_length_eq_one_of_sat_49a382efb70e
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:24:54.654856+00:00
-- url     : https://prove2.me/theorems/44b5cf84-4b31-41af-91da-7b6e12fa7488
-- title:
--   P2 M Ground Theory Heights  Heights Inter Diagonal Order One length eq one of sat 49a382efb70e: P2 M Ground Theory Heights  Heights Inter Diagonal Order One length eq one of sat 49a382efb70e
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Diagonal Order One length eq one of sat 49a382efb70e construction uses the P2 M Ground Theory Heights  Heights Inter Diagonal Order One length eq one of sat 49a382efb70e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagOrdOne.lean#L18-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagOrdOne.lean#L18-L70

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagFormDiv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PPFFibreSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDiagOrdOne
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.DiagonalOrderOne
variable {A : Type*} [CommRing A]

theorem P2M_GroundTheory_Heights__Heights_Inter_DiagonalOrderOne_length_eq_one_of_sat_49a382efb70e (J W : Ideal A) [W.IsPrime] (hJ : J ≤ W) (hs : ∀ d ∈ W, ∃ u ∉ W, u * d ∈ J) :
    Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (A ⧸ J)) = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«DiagonalOrderOne».«length_eq_one_of_sat» := P2M_GroundTheory_Heights__Heights_Inter_DiagonalOrderOne_length_eq_one_of_sat_49a382efb70e
