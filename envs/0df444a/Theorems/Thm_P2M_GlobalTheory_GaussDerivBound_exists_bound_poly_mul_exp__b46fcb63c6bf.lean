-- Prove2me | Theorems.Thm_P2M_GlobalTheory_GaussDerivBound_exists_bound_poly_mul_exp__b46fcb63c6bf
-- name    : P2M_GlobalTheory_GaussDerivBound_exists_bound_poly_mul_exp__b46fcb63c6bf
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T00:06:03.972437+00:00
-- url     : https://prove2.me/theorems/d3075609-f652-4fb7-9451-c9a192f25687
-- title:
--   P2 M Global Theory Gauss Deriv Bound exists bound poly mul exp  b46fcb63c6bf: P2 M Global Theory Gauss Deriv Bound exists bound poly mul exp  b46fcb63c6bf
-- statement:
--   The P2 M Global Theory Gauss Deriv Bound exists bound poly mul exp  b46fcb63c6bf construction uses the P2 M Global Theory Gauss Deriv Bound exists bound poly mul exp  b46fcb63c6bf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GaussianIteratedFDerivWeightedExpBounded.lean#L53-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GaussianIteratedFDerivWeightedExpBounded.lean#L53-L61

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PowForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PolyMulGaussianBounded
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussianIteratedFDerivWeightedExpBounded
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.GaussDerivBound
open scoped Nat
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem P2M_GlobalTheory_GaussDerivBound_exists_bound_poly_mul_exp__b46fcb63c6bf (c : ℝ) (hc : 0 < c) (N : ℕ) :
    ∃ C, ∀ r : ℝ, 0 ≤ r → (1 + r) ^ N * Real.exp (-(c * r ^ 2)) ≤ C := by sorry

alias «GlobalTheory».«GaussDerivBound».«exists_bound_poly_mul_exp'» := P2M_GlobalTheory_GaussDerivBound_exists_bound_poly_mul_exp__b46fcb63c6bf
