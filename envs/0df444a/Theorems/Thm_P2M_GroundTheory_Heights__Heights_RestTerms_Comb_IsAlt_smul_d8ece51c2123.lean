-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Comb_IsAlt_smul_d8ece51c2123
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Comb_IsAlt_smul_d8ece51c2123
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:18:52.469739+00:00
-- url     : https://prove2.me/theorems/318e0501-bdd1-4d27-9935-c8682161187f
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Comb Is Alt smul d8ece51c2123: P2 M Ground Theory Heights  Heights Rest Terms Comb Is Alt smul d8ece51c2123
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Comb Is Alt smul d8ece51c2123 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Comb Is Alt smul d8ece51c2123 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/AltCoeff.lean#L184-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/AltCoeff.lean#L184-L185

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_VandermondeOfEqDet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_AltCoeff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms GroundTheory.Heights₂.Heights.RestTerms.Comb
open MvPolynomial Finset Equiv
noncomputable section
variable {m : ℕ}

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Comb_IsAlt_smul_d8ece51c2123 {P : MvPolynomial (Fin m) ℚ} (hP : IsAlt P) (c : ℚ) : IsAlt (c • P) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Comb».«IsAlt».«smul» := P2M_GroundTheory_Heights__Heights_RestTerms_Comb_IsAlt_smul_d8ece51c2123
