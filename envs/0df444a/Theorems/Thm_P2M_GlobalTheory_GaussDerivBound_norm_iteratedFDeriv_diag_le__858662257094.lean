-- Prove2me | Theorems.Thm_P2M_GlobalTheory_GaussDerivBound_norm_iteratedFDeriv_diag_le__858662257094
-- name    : P2M_GlobalTheory_GaussDerivBound_norm_iteratedFDeriv_diag_le__858662257094
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:06:18.929329+00:00
-- url     : https://prove2.me/theorems/7487643e-4048-4b3e-8e18-27628f7a0f8e
-- title:
--   P2 M Global Theory Gauss Deriv Bound norm iterated FDeriv diag le  858662257094: P2 M Global Theory Gauss Deriv Bound norm iterated FDeriv diag le  858662257094
-- statement:
--   The P2 M Global Theory Gauss Deriv Bound norm iterated FDeriv diag le  858662257094 construction uses the P2 M Global Theory Gauss Deriv Bound norm iterated FDeriv diag le  858662257094 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GaussianIteratedFDerivWeightedExpBounded.lean#L27-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GaussianIteratedFDerivWeightedExpBounded.lean#L27-L44

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

theorem P2M_GlobalTheory_GaussDerivBound_norm_iteratedFDeriv_diag_le__858662257094 (B : E →L[ℝ] E →L[ℝ] ℝ) (n : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ n (fun y => B y y) x‖ ≤ ‖B‖ * (2 ^ n * (1 + ‖x‖) ^ 2) := by sorry

alias «GlobalTheory».«GaussDerivBound».«norm_iteratedFDeriv_diag_le'» := P2M_GlobalTheory_GaussDerivBound_norm_iteratedFDeriv_diag_le__858662257094
