-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_genFibQuot_mk_df9bf3ed9b82
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_genFibQuot_mk_df9bf3ed9b82
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:10:44.383041+00:00
-- url     : https://prove2.me/theorems/2f8cb483-1bc6-4e39-a246-464caafeadf1
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR gen Fib Quot mk df9bf3ed9b82: P2 M Ground Theory Heights  Heights Numbers DVR gen Fib Quot mk df9bf3ed9b82
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR gen Fib Quot mk df9bf3ed9b82 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR gen Fib Quot mk df9bf3ed9b82 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PGenericPieceRank.lean#L39-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PGenericPieceRank.lean#L39-L41

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PGenericPieceRank
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
variable {O : Type*} [CommRing O] [IsDomain O] {K : Type*} [DecidableEq K] {ι : K → Type*}
omit [IsDomain O] [DecidableEq K]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_genFibQuot_mk_df9bf3ed9b82 (P : Ideal (MRing ι O)) (g : MRing ι O) :
    genFibQuot P (Ideal.Quotient.mk P g) =
      Ideal.Quotient.mk (genFib P) (map (algebraMap O (FractionRing O)) g) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«genFibQuot_mk» := P2M_GroundTheory_Heights__Heights_NumbersDVR_genFibQuot_mk_df9bf3ed9b82
