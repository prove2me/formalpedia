-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_coeff_aeval_one_add_X_pow_sub_one_ne_zero__677c239f9cf3
-- name    : P2M_GlobalTheory_T_coeff_aeval_one_add_X_pow_sub_one_ne_zero__677c239f9cf3
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T00:08:54.570501+00:00
-- url     : https://prove2.me/theorems/215b2a63-b7dd-4c0c-8f39-12343e172576
-- title:
--   P2 M Global Theory T coeff aeval one add X pow sub one ne zero  677c239f9cf3: P2 M Global Theory T coeff aeval one add X pow sub one ne zero  677c239f9cf3
-- statement:
--   The P2 M Global Theory T coeff aeval one add X pow sub one ne zero  677c239f9cf3 construction uses the P2 M Global Theory T coeff aeval one add X pow sub one ne zero  677c239f9cf3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CoeffAevalOneAddXPowSubOneNeZeroStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CoeffAevalOneAddXPowSubOneNeZeroStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CoeffAevalOneAddXPowSubOneNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CoeffAevalOneAddXPowSubOneNeZeroStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_coeff_aeval_one_add_X_pow_sub_one_ne_zero__677c239f9cf3 : ∀ (k σ : Type) [Field k] [Fintype σ] (l M : ℕ) [Fact l.Prime] [CharP k l] (D u : MvPolynomial σ k) (n e : σ → ℕ), u.coeff 0 ≠ 0 → D - u * ∏ q, MvPolynomial.X q ^ n q ∈ Ideal.span (Set.range fun q : σ => (MvPolynomial.X q : MvPolynomial σ k) ^ (l ^ M)) → ∑ q, n q * l ^ e q < l ^ M → (MvPolynomial.aeval (fun q => (1 + Polynomial.X : Polynomial k) ^ (l ^ e q) - 1) D).coeff (∑ q, n q * l ^ e q) ≠ 0 := by sorry

alias «GlobalTheory».«T».«coeff_aeval_one_add_X_pow_sub_one_ne_zero'» := P2M_GlobalTheory_T_coeff_aeval_one_add_X_pow_sub_one_ne_zero__677c239f9cf3
