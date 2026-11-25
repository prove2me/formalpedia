-- Prove2me | Theorems.Thm_P2M_GlobalTheory_GaussDerivBound_norm_iteratedFDeriv_rexp__05ab81754a94
-- name    : P2M_GlobalTheory_GaussDerivBound_norm_iteratedFDeriv_rexp__05ab81754a94
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:06:25.222583+00:00
-- url     : https://prove2.me/theorems/a4fc7a7b-93fb-40fe-af88-3fd22c79a8bd
-- title:
--   P2 M Global Theory Gauss Deriv Bound norm iterated FDeriv rexp  05ab81754a94: P2 M Global Theory Gauss Deriv Bound norm iterated FDeriv rexp  05ab81754a94
-- statement:
--   The P2 M Global Theory Gauss Deriv Bound norm iterated FDeriv rexp  05ab81754a94 construction uses the P2 M Global Theory Gauss Deriv Bound norm iterated FDeriv rexp  05ab81754a94 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GaussianIteratedFDerivWeightedExpBounded.lean#L46-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GaussianIteratedFDerivWeightedExpBounded.lean#L46-L51

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

theorem P2M_GlobalTheory_GaussDerivBound_norm_iteratedFDeriv_rexp__05ab81754a94 (i : ℕ) (y : ℝ) : ‖iteratedFDeriv ℝ i Real.exp y‖ = Real.exp y := by sorry

alias «GlobalTheory».«GaussDerivBound».«norm_iteratedFDeriv_rexp'» := P2M_GlobalTheory_GaussDerivBound_norm_iteratedFDeriv_rexp__05ab81754a94
