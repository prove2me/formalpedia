-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Comb_alt_isAlt_9f813e5016fd
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Comb_alt_isAlt_9f813e5016fd
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T11:29:44.986721+00:00
-- url     : https://prove2.me/theorems/8305ef68-ad44-4490-95ef-0ec30706aa59
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Comb alt is Alt 9f813e5016fd: P2 M Ground Theory Heights  Heights Rest Terms Comb alt is Alt 9f813e5016fd
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Comb alt is Alt 9f813e5016fd construction uses the P2 M Ground Theory Heights  Heights Rest Terms Comb alt is Alt 9f813e5016fd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/AltCoeff.lean#L46-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/AltCoeff.lean#L46-L46

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Comb_alt_isAlt_9f813e5016fd (v : Fin m → ℕ) : IsAlt (alt v) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Comb».«alt_isAlt» := P2M_GroundTheory_Heights__Heights_RestTerms_Comb_alt_isAlt_9f813e5016fd
