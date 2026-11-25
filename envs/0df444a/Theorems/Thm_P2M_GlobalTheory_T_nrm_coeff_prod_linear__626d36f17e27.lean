-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_nrm_coeff_prod_linear__626d36f17e27
-- name    : P2M_GlobalTheory_T_nrm_coeff_prod_linear__626d36f17e27
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:15:22.800443+00:00
-- url     : https://prove2.me/theorems/fd6ea74e-b327-54a8-8687-ffe1a946ef96
-- title:
--   P2 M Global Theory T nrm coeff prod linear  626d36f17e27: P2 M Global Theory T nrm coeff prod linear  626d36f17e27
-- statement:
--   The P2 M Global Theory T nrm coeff prod linear  626d36f17e27 construction uses the P2 M Global Theory T nrm coeff prod linear  626d36f17e27 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NrmCoeffProdLinearStatement.lean#L10-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NrmCoeffProdLinearStatement.lean#L10-L11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NrmCoeffProdLinear
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NrmCoeffProdLinearStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef
set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_nrm_coeff_prod_linear__626d36f17e27 : ∀ (k F : Type) [Field k] [Field F] [Algebra k F], ∀ (v : Place k F) (m : ℕ) (α β : Fin m → F), nrm v (fun a : Fin (m + 1) => (∏ j, (Polynomial.C (α j) + Polynomial.C (β j) * Polynomial.X)).coeff a) = ∏ j, max (v.1 (α j)) (v.1 (β j)) := by sorry

alias «GlobalTheory».«T».«nrm_coeff_prod_linear'» := P2M_GlobalTheory_T_nrm_coeff_prod_linear__626d36f17e27
