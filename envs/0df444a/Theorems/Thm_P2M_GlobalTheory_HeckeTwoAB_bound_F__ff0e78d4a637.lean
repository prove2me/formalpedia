-- Prove2me | Theorems.Thm_P2M_GlobalTheory_HeckeTwoAB_bound_F__ff0e78d4a637
-- name    : P2M_GlobalTheory_HeckeTwoAB_bound_F__ff0e78d4a637
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:06:19.775001+00:00
-- url     : https://prove2.me/theorems/11f73d58-41c3-41d4-ad87-2d0894a7e6c6
-- title:
--   P2 M Global Theory Hecke Two AB bound F  ff0e78d4a637: P2 M Global Theory Hecke Two AB bound F  ff0e78d4a637
-- statement:
--   The P2 M Global Theory Hecke Two AB bound F  ff0e78d4a637 construction uses the P2 M Global Theory Hecke Two AB bound F  ff0e78d4a637 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckeHankelTransformABDifferentiableOnSigma.lean#L95-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckeHankelTransformABDifferentiableOnSigma.lean#L95-L124

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HTransABTwoZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckePhiFourierConstantAtZeroDifferentiableOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeHankelTransformABDifferentiableOnSigma
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
noncomputable section
open GlobalTheory GlobalTheory.HeckeTwoAB
open MeasureTheory GlobalTheory.HeckeTwoC

theorem P2M_GlobalTheory_HeckeTwoAB_bound_F__ff0e78d4a637 {ε M : ℝ} (hε : 0 < ε) (a b : ℕ) (ν : ℝ) {y : ℝ} (hy : y ≠ 0) {σ : ℂ}
    (hc : 1 + 2 * ε ≤ (a + b : ℝ) + 2 * σ.re) (hM : (a + b : ℝ) + 2 * σ.re ≤ M) (t : ℝ) :
    ‖F' a b ν y σ t‖ ≤
      2 * Real.exp (M * |Real.log (abs y)|) * (|Real.log (abs y)| + 1 / ε) * Real.exp (-(1 + ε) * lg (t / y)) := by sorry

alias «GlobalTheory».«HeckeTwoAB».«bound_F'» := P2M_GlobalTheory_HeckeTwoAB_bound_F__ff0e78d4a637
