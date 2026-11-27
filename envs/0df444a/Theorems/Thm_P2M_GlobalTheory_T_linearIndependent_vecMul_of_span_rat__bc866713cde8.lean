-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_linearIndependent_vecMul_of_span_rat__bc866713cde8
-- name    : P2M_GlobalTheory_T_linearIndependent_vecMul_of_span_rat__bc866713cde8
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:06:29.775154+00:00
-- url     : https://prove2.me/theorems/acfcb225-7d8e-5417-94aa-93d82351528a
-- title:
--   P2 M Global Theory T linear Independent vec Mul of span rat  bc866713cde8: P2 M Global Theory T linear Independent vec Mul of span rat  bc866713cde8
-- statement:
--   The P2 M Global Theory T linear Independent vec Mul of span rat  bc866713cde8 construction uses the P2 M Global Theory T linear Independent vec Mul of span rat  bc866713cde8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/LinearIndependentVecMulOfSpanRatStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/LinearIndependentVecMulOfSpanRatStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LinearIndependentVecMulOfSpanRat
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LinearIndependentVecMulOfSpanRatStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_linearIndependent_vecMul_of_span_rat__bc866713cde8 : ∀ (E : Type) [Field E] [NumberField E] (R : Type) [CommRing R] [Algebra ℝ R] [FiniteDimensional ℝ R] (τ : E →+* R), Submodule.span ℝ (Set.range τ) = ⊤ → Module.finrank ℝ R = Module.finrank ℚ E → ∀ (n : ℕ) (ι : Type) [Fintype ι] (u : ι → Fin n → E), Fintype.card ι = Module.finrank ℚ E * n → Submodule.span ℚ (Set.range u) = ⊤ → ∀ g : GL (Fin n) R, LinearIndependent ℝ fun k => (fun i => τ (u k i)) ᵥ* g.1 := by sorry

alias «GlobalTheory».«T».«linearIndependent_vecMul_of_span_rat'» := P2M_GlobalTheory_T_linearIndependent_vecMul_of_span_rat__bc866713cde8
