-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Comb_cf_perm_129463b0e566
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Comb_cf_perm_129463b0e566
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T11:30:24.696985+00:00
-- url     : https://prove2.me/theorems/a2bb3cc5-03fe-442e-8b69-6f7a74b209bc
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Comb cf perm 129463b0e566: P2 M Ground Theory Heights  Heights Rest Terms Comb cf perm 129463b0e566
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Comb cf perm 129463b0e566 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Comb cf perm 129463b0e566 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/AltCoeff.lean#L52-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/AltCoeff.lean#L52-L58

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Comb_cf_perm_129463b0e566 {P : MvPolynomial (Fin m) ℚ} (hP : IsAlt P) (σ : Perm (Fin m)) (v : Fin m → ℕ) :
    cf (v ∘ σ.symm) P = ((Perm.sign σ : ℤ) : ℚ) * cf v P := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Comb».«cf_perm» := P2M_GroundTheory_Heights__Heights_RestTerms_Comb_cf_perm_129463b0e566
