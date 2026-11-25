-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Comb_isSymmetric_prod_psum_0553020b3d1e
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Comb_isSymmetric_prod_psum_0553020b3d1e
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:18:52.69566+00:00
-- url     : https://prove2.me/theorems/4f40a3de-f42b-4301-a83f-2cf2aca7f8a5
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Comb is Symmetric prod psum 0553020b3d1e: P2 M Ground Theory Heights  Heights Rest Terms Comb is Symmetric prod psum 0553020b3d1e
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Comb is Symmetric prod psum 0553020b3d1e construction uses the P2 M Ground Theory Heights  Heights Rest Terms Comb is Symmetric prod psum 0553020b3d1e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/AltCoeff.lean#L198-L202
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/AltCoeff.lean#L198-L202

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Comb_isSymmetric_prod_psum_0553020b3d1e (ρ : List ℕ) :
    ((ρ.map fun q => psum (Fin m) ℚ q).prod).IsSymmetric := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Comb».«isSymmetric_prod_psum» := P2M_GroundTheory_Heights__Heights_RestTerms_Comb_isSymmetric_prod_psum_0553020b3d1e
