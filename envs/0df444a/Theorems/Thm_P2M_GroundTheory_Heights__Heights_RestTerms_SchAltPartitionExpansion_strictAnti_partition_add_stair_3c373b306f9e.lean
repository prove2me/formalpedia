-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_SchAltPartitionExpansion_strictAnti_partition_add_stair_3c373b306f9e
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_SchAltPartitionExpansion_strictAnti_partition_add_stair_3c373b306f9e
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:20:36.72412+00:00
-- url     : https://prove2.me/theorems/77e654b4-38da-4de9-9a32-c9e4b6d92da4
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Sch Alt Partition Expansion strict Anti partition add stair 3c373b306f9e: P2 M Ground Theory Heights  Heights Rest Terms Sch Alt Partition Expansion stri
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Sch Alt Partition Expansion strict Anti partition add stair 3c373b306f9e construction uses the P2 M Ground Theory Heights  Heights Rest Terms Sch Alt Partition Expansion strict Anti partition add stair 3c373b306f9e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PSchAltPartitionExpansion.lean#L21-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PSchAltPartitionExpansion.lean#L21-L30

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsSchur
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_JacobiTrudi
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_AltCoeff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PSchAltPartitionExpansion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial Finset
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_RestTerms_SchAltPartitionExpansion_strictAnti_partition_add_stair_3c373b306f9e {r n : ℕ} {lam : Fin r → ℕ} (hlam : lam ∈ partitionsOf r n) :
    StrictAnti (fun i : Fin r => lam i + (r - 1 - (i : ℕ))) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«SchAltPartitionExpansion».«strictAnti_partition_add_stair» := P2M_GroundTheory_Heights__Heights_RestTerms_SchAltPartitionExpansion_strictAnti_partition_add_stair_3c373b306f9e
