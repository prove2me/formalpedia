-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Comb_ex_comp_symm_9ec9c9f85fff
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Comb_ex_comp_symm_9ec9c9f85fff
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:18:35.776257+00:00
-- url     : https://prove2.me/theorems/b5a53400-56b9-5128-aaa5-b8bebd9d17ff
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Comb ex comp symm 9ec9c9f85fff: P2 M Ground Theory Heights  Heights Rest Terms Comb ex comp symm 9ec9c9f85fff
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Comb ex comp symm 9ec9c9f85fff construction uses the P2 M Ground Theory Heights  Heights Rest Terms Comb ex comp symm 9ec9c9f85fff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/AltCoeff.lean#L26-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/AltCoeff.lean#L26-L31

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Comb_ex_comp_symm_9ec9c9f85fff (v : Fin m → ℕ) (σ : Perm (Fin m)) :
    Finsupp.mapDomain σ (ex v) = ex (v ∘ σ.symm) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Comb».«ex_comp_symm» := P2M_GroundTheory_Heights__Heights_RestTerms_Comb_ex_comp_symm_9ec9c9f85fff
