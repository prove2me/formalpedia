-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_SchAltPartitionExpansion_alt_partition_add_stair_eq_ef5b2bd149cf
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_SchAltPartitionExpansion_alt_partition_add_stair_eq_ef5b2bd149cf
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:20:37.973098+00:00
-- url     : https://prove2.me/theorems/b2e3b2ee-0755-5d76-8a29-63b8e7775cfc
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Sch Alt Partition Expansion alt partition add stair eq ef5b2bd149cf: P2 M Ground Theory Heights  Heights Rest Terms Sch Alt Partition Expansion alt parti
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Sch Alt Partition Expansion alt partition add stair eq ef5b2bd149cf construction uses the P2 M Ground Theory Heights  Heights Rest Terms Sch Alt Partition Expansion alt partition add stair eq ef5b2bd149cf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PSchAltPartitionExpansion.lean#L14-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PSchAltPartitionExpansion.lean#L14-L19

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_SchAltPartitionExpansion_alt_partition_add_stair_eq_ef5b2bd149cf {r : ℕ} (lam : Fin r → ℕ) :
    Comb.alt (fun i : Fin r => lam i + (r - 1 - (i : ℕ))) =
      vandermondeOf (fun i : Fin r => (X i : MvPolynomial (Fin r) ℚ)) * schur (Fin r) lam := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«SchAltPartitionExpansion».«alt_partition_add_stair_eq» := P2M_GroundTheory_Heights__Heights_RestTerms_SchAltPartitionExpansion_alt_partition_add_stair_eq_ef5b2bd149cf
