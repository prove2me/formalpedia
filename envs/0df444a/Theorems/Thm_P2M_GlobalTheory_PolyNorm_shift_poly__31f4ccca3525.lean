-- Prove2me | Theorems.Thm_P2M_GlobalTheory_PolyNorm_shift_poly__31f4ccca3525
-- name    : P2M_GlobalTheory_PolyNorm_shift_poly__31f4ccca3525
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T00:08:32.460238+00:00
-- url     : https://prove2.me/theorems/79e261ce-979d-4319-af8e-e4d786db402c
-- title:
--   P2 M Global Theory Poly Norm shift poly  31f4ccca3525: P2 M Global Theory Poly Norm shift poly  31f4ccca3525
-- statement:
--   The P2 M Global Theory Poly Norm shift poly  31f4ccca3525 construction uses the P2 M Global Theory Poly Norm shift poly  31f4ccca3525 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/EqProdOfMul.lean#L64-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/EqProdOfMul.lean#L64-L72

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EqOfNormResultantEqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EqProdOfMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.PolyNorm
variable (N : ℤ[X] → ℚ) (Φ : (r : ℕ) → MvPolynomial (Fin r) ℚ)
  (hN : ∀ r (F : ℤ[X]), F.natDegree < r → N F = ev (Φ r) (F.map (Int.castRingHom ℚ)))
include hN

theorem P2M_GlobalTheory_PolyNorm_shift_poly__31f4ccca3525 (F G : ℤ[X]) :
    ∃ p : ℚ[X], ∀ t : ℕ, N ((F + t) * (G + t)) = p.eval (t : ℚ) := by sorry

alias «GlobalTheory».«PolyNorm».«shift_poly₂» := P2M_GlobalTheory_PolyNorm_shift_poly__31f4ccca3525
