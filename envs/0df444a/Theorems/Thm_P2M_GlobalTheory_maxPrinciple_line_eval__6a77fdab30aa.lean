-- Prove2me | Theorems.Thm_P2M_GlobalTheory_maxPrinciple_line_eval__6a77fdab30aa
-- name    : P2M_GlobalTheory_maxPrinciple_line_eval__6a77fdab30aa
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T00:12:40.158499+00:00
-- url     : https://prove2.me/theorems/b208738c-e006-431e-9d06-5d256ca53d7c
-- title:
--   P2 M Global Theory max Principle line eval  6a77fdab30aa: P2 M Global Theory max Principle line eval  6a77fdab30aa
-- statement:
--   The P2 M Global Theory max Principle line eval  6a77fdab30aa construction uses the P2 M Global Theory max Principle line eval  6a77fdab30aa property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PolynomialEvalBoundOnCircleFamily.lean#L161-L293
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PolynomialEvalBoundOnCircleFamily.lean#L161-L293

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsRootMapMinpolyIffExistsRingHomExtensionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PolynomialEvalBoundOnCircleFamily
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open MvPolynomial
open MvPolynomial

theorem P2M_GlobalTheory_maxPrinciple_line_eval__6a77fdab30aa : ∀ (d : ℕ) (B : Type) [CommRing B] [IsDomain B] [Algebra (MvPolynomial (Fin d) ℚ) B] [Module.Finite (MvPolynomial (Fin d) ℚ) B], Function.Injective (algebraMap (MvPolynomial (Fin d) ℚ) B) → ∀ (r : ℕ) (G : MvPolynomial (Fin r) B) (c : Fin r → ℂ) (z v : Fin d → ℂ) (R : ℝ), (∀ (x : B →+* ℂ) (w : ℂ), ‖w‖ = 1 → (∀ i, x (algebraMap (MvPolynomial (Fin d) ℚ) B (MvPolynomial.X i)) = z i + w * v i) → ‖MvPolynomial.eval₂ x c G‖ ≤ R) → ∀ x : B →+* ℂ, (∀ i, x (algebraMap (MvPolynomial (Fin d) ℚ) B (MvPolynomial.X i)) = z i) → ‖MvPolynomial.eval₂ x c G‖ ≤ R := by sorry

alias «GlobalTheory».«maxPrinciple_line_eval₂» := P2M_GlobalTheory_maxPrinciple_line_eval__6a77fdab30aa
