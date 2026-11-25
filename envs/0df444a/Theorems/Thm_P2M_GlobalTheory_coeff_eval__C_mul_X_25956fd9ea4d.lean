-- Prove2me | Theorems.Thm_P2M_GlobalTheory_coeff_eval__C_mul_X_25956fd9ea4d
-- name    : P2M_GlobalTheory_coeff_eval__C_mul_X_25956fd9ea4d
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:12:01.778136+00:00
-- url     : https://prove2.me/theorems/7d38a9d2-2133-484f-af32-e33da63d3d0c
-- title:
--   P2 M Global Theory coeff eval  C mul X 25956fd9ea4d: P2 M Global Theory coeff eval  C mul X 25956fd9ea4d
-- statement:
--   The P2 M Global Theory coeff eval  C mul X 25956fd9ea4d construction uses the P2 M Global Theory coeff eval  C mul X 25956fd9ea4d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HomogeneousComponentsOfConeIntegralEquation.lean#L6-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HomogeneousComponentsOfConeIntegralEquation.lean#L6-L35

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HomogeneousComponentsOfConeIntegralEquation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open GlobalTheory

theorem P2M_GlobalTheory_coeff_eval__C_mul_X_25956fd9ea4d {F K : Type} [Field F] [Field K] (φ : F →+* K) {r : ℕ} (w : Fin r → K)
    (p : MvPolynomial (Fin r) F) (d : ℕ) :
    (MvPolynomial.eval₂ (Polynomial.C.comp φ) (fun i => Polynomial.C (w i) * Polynomial.X) p).coeff d
      = MvPolynomial.eval₂ φ w (homogeneousComponent d p) := by sorry

alias «GlobalTheory».«coeff_eval₂_C_mul_X» := P2M_GlobalTheory_coeff_eval__C_mul_X_25956fd9ea4d
