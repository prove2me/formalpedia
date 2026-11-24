-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_inh_decomp_c8d39b1d7eb7
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_inh_decomp_c8d39b1d7eb7
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:32:42.747263+00:00
-- url     : https://prove2.me/theorems/03478fa7-7d56-486e-923f-4635534f1ab2
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms inh decomp c8d39b1d7eb7: P2 M Ground Theory Heights  Heights Rest Terms inh decomp c8d39b1d7eb7
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms inh decomp c8d39b1d7eb7 construction uses the P2 M Ground Theory Heights  Heights Rest Terms inh decomp c8d39b1d7eb7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/Inhabitants.lean#L27-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/Inhabitants.lean#L27-L35

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Inhabitants
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
open MvPolynomial
noncomputable section
open MvPolynomial

theorem P2M_GroundTheory_Heights__Heights_RestTerms_inh_decomp_c8d39b1d7eb7 : IsPowerSumDecomposition 1 (1+1) (restPolynomial 1 1 1 .last)
    (fun k _ => if k = 1 then C (2⁻¹) * (flagTwoSecondRoot - flagTwoFirstRoot) else if k = 2 then C (2⁻¹) else 0) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«inh_decomp» := P2M_GroundTheory_Heights__Heights_RestTerms_inh_decomp_c8d39b1d7eb7
