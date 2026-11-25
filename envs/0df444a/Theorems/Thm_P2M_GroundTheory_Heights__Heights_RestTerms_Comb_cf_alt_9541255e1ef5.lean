-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Comb_cf_alt_9541255e1ef5
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Comb_cf_alt_9541255e1ef5
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:18:55.951727+00:00
-- url     : https://prove2.me/theorems/7b89f0fa-ce93-4d21-94cb-ca2f92806f98
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Comb cf alt 9541255e1ef5: P2 M Ground Theory Heights  Heights Rest Terms Comb cf alt 9541255e1ef5
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Comb cf alt 9541255e1ef5 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Comb cf alt 9541255e1ef5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/AltCoeff.lean#L104-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/AltCoeff.lean#L104-L108

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Comb_cf_alt_9541255e1ef5 (l v : Fin m → ℕ) :
    cf l (alt v) = ∑ σ : Perm (Fin m), ((Perm.sign σ : ℤ) : ℚ) * if l = v ∘ σ.symm then 1 else 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Comb».«cf_alt» := P2M_GroundTheory_Heights__Heights_RestTerms_Comb_cf_alt_9541255e1ef5
