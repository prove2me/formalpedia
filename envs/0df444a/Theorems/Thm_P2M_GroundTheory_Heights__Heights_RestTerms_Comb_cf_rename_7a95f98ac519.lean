-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Comb_cf_rename_7a95f98ac519
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Comb_cf_rename_7a95f98ac519
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:18:47.589146+00:00
-- url     : https://prove2.me/theorems/963bac53-b3b6-43e0-9deb-2cc205410349
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Comb cf rename 7a95f98ac519: P2 M Ground Theory Heights  Heights Rest Terms Comb cf rename 7a95f98ac519
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Comb cf rename 7a95f98ac519 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Comb cf rename 7a95f98ac519 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/AltCoeff.lean#L33-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/AltCoeff.lean#L33-L36

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Comb_cf_rename_7a95f98ac519 (v : Fin m → ℕ) (σ : Perm (Fin m)) (P : MvPolynomial (Fin m) ℚ) :
    cf (v ∘ σ.symm) (rename σ P) = cf v P := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Comb».«cf_rename» := P2M_GroundTheory_Heights__Heights_RestTerms_Comb_cf_rename_7a95f98ac519
