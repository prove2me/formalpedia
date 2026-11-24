-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Comb_isAlt_vandermonde_mul_prod_b74d8ff779cf
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Comb_isAlt_vandermonde_mul_prod_b74d8ff779cf
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T18:11:22.678738+00:00
-- url     : https://prove2.me/theorems/465e1ff4-d83d-40c3-b780-65692a4f040c
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Comb is Alt vandermonde mul prod b74d8ff779cf: P2 M Ground Theory Heights  Heights Rest Terms Comb is Alt vandermonde mul prod b74d8ff779cf
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Comb is Alt vandermonde mul prod b74d8ff779cf construction uses the P2 M Ground Theory Heights  Heights Rest Terms Comb is Alt vandermonde mul prod b74d8ff779cf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/AltCoeff.lean#L204-L208
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/AltCoeff.lean#L204-L208

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Comb_isAlt_vandermonde_mul_prod_b74d8ff779cf (ρ : List ℕ) :
    IsAlt (vandermondeOf (fun i : Fin m => (X i : MvPolynomial (Fin m) ℚ)) *
      (ρ.map fun q => psum (Fin m) ℚ q).prod) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Comb».«isAlt_vandermonde_mul_prod» := P2M_GroundTheory_Heights__Heights_RestTerms_Comb_isAlt_vandermonde_mul_prod_b74d8ff779cf
