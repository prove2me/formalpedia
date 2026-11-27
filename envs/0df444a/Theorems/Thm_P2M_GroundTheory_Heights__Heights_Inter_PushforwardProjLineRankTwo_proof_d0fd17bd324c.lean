-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PushforwardProjLineRankTwo_proof_d0fd17bd324c
-- name    : P2M_GroundTheory_Heights__Heights_Inter_PushforwardProjLineRankTwo_proof_d0fd17bd324c
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T13:26:55.526579+00:00
-- url     : https://prove2.me/theorems/4903f010-6c3e-480e-8382-dee4a19cc874
-- title:
--   P2 M Ground Theory Heights  Heights Inter Pushforward Proj Line Rank Two proof d0fd17bd324c: P2 M Ground Theory Heights  Heights Inter Pushforward Proj Line Rank Two proof d0fd17bd324c
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Pushforward Proj Line Rank Two proof d0fd17bd324c construction uses the P2 M Ground Theory Heights  Heights Inter Pushforward Proj Line Rank Two proof d0fd17bd324c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PrimePairSetFirst.lean#L13-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PrimePairSetFirst.lean#L13-L29

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_ExistsUniqueStatement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsLineFibre
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PrimePairSetFirst
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem P2M_GroundTheory_Heights__Heights_Inter_PushforwardProjLineRankTwo_proof_d0fd17bd324c (hPF : PushforwardProjLineFlag.Statement) (hF : FibreDimStatement)
    (hR4 : ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)],
      ExistsUniqueStatement F ι)
    (hLine : LineFibreBlocks.Statement) : PushforwardProjLineRankTwo.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«PushforwardProjLineRankTwo».«proof» := P2M_GroundTheory_Heights__Heights_Inter_PushforwardProjLineRankTwo_proof_d0fd17bd324c
