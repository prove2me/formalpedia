-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagonalOrder_multAt_eq_zero_of_not_le_a33d6d2519c2
-- name    : P2M_GroundTheory_Heights__Heights_Inter_DiagonalOrder_multAt_eq_zero_of_not_le_a33d6d2519c2
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:29:31.244809+00:00
-- url     : https://prove2.me/theorems/ddb21e99-ea26-50c3-8465-9795c576b338
-- title:
--   P2 M Ground Theory Heights  Heights Inter Diagonal Order mult At eq zero of not le a33d6d2519c2: P2 M Ground Theory Heights  Heights Inter Diagonal Order mult At eq zero of not le a33d6d2519c2
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Diagonal Order mult At eq zero of not le a33d6d2519c2 construction uses the P2 M Ground Theory Heights  Heights Inter Diagonal Order mult At eq zero of not le a33d6d2519c2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagOrd.lean#L22-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagOrd.lean#L22-L26

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagDiv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagOffUnit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagOrdOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagRelevant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRFormula
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDiagOrd
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
open GroundTheory.Heights₂.Heights.Inter.DiagonalOrder
variable {K : Type} {ι : K → Type}

theorem P2M_GroundTheory_Heights__Heights_Inter_DiagonalOrder_multAt_eq_zero_of_not_le_a33d6d2519c2 {J W : Ideal (MRing ι)} (hW : W.IsPrime) (h : ¬ J ≤ W) : multAt J W = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«DiagonalOrder».«multAt_eq_zero_of_not_le» := P2M_GroundTheory_Heights__Heights_Inter_DiagonalOrder_multAt_eq_zero_of_not_le_a33d6d2519c2
