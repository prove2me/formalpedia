-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Flag_exists_powerSumHom_eq_7cf93073418c
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Flag_exists_powerSumHom_eq_7cf93073418c
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:31:41.566179+00:00
-- url     : https://prove2.me/theorems/c9fb2d1b-56c3-480d-87e0-2c8c4fa15ab2
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Flag exists power Sum Hom eq 7cf93073418c: P2 M Ground Theory Heights  Heights Rest Terms Flag exists power Sum Hom eq 7cf93073418c
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Flag exists power Sum Hom eq 7cf93073418c construction uses the P2 M Ground Theory Heights  Heights Rest Terms Flag exists power Sum Hom eq 7cf93073418c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PowerSums.lean#L65-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PowerSums.lean#L65-L78

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PowerSums
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.RestTerms
open GroundTheory.Heights₂.Heights.RestTerms.Flag
open MvPolynomial Finset
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Flag_exists_powerSumHom_eq_7cf93073418c {N : ℕ} {P : MvPolynomial (Fin N) ℚ} (hP : P.IsSymmetric) :
    ∃ S, powerSumHom N S = P := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Flag».«exists_powerSumHom_eq» := P2M_GroundTheory_Heights__Heights_RestTerms_Flag_exists_powerSumHom_eq_7cf93073418c
