-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_mem_polyring_of_integral_closure_range__97cef6d2bba2
-- name    : P2M_GlobalTheory_T_mem_polyring_of_integral_closure_range__97cef6d2bba2
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T13:06:45.740219+00:00
-- url     : https://prove2.me/theorems/998dddea-b8cf-4cb6-9494-cd28496995f8
-- title:
--   P2 M Global Theory T mem polyring of integral closure range  97cef6d2bba2: P2 M Global Theory T mem polyring of integral closure range  97cef6d2bba2
-- statement:
--   The P2 M Global Theory T mem polyring of integral closure range  97cef6d2bba2 construction uses the P2 M Global Theory T mem polyring of integral closure range  97cef6d2bba2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemPolyringOfIntegralClosureRangeStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemPolyringOfIntegralClosureRangeStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemPolyringOfIntegralClosureRange
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemPolyringOfIntegralClosureRangeStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_mem_polyring_of_integral_closure_range__97cef6d2bba2 : ∀ {K : Type} [Field K] {D : ℕ} (y : Fin D → K), AlgebraicIndependent ℤ y → ∀ (t : K), t ∈ Subfield.closure (Set.range y) → ∀ {ι : Type} (z : ι → K), (∀ i, ∃ p : MvPolynomial (Fin D) ℤ, aeval y p = z i) → ∀ (f : Polynomial (MvPolynomial ι ℤ)), f.Monic → f.eval₂ (aeval z).toRingHom t = 0 → ∃ T₀ : MvPolynomial (Fin D) ℤ, t = aeval y T₀ := by sorry

alias «GlobalTheory».«T».«mem_polyring_of_integral_closure_range'» := P2M_GlobalTheory_T_mem_polyring_of_integral_closure_range__97cef6d2bba2
