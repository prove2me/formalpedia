-- Prove2me | Theorems.Thm_P2M_GlobalTheory_HeckeTwoC_norm_G__1a9e454f2caf
-- name    : P2M_GlobalTheory_HeckeTwoC_norm_G__1a9e454f2caf
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T00:05:53.158671+00:00
-- url     : https://prove2.me/theorems/99a7b780-503a-4f74-aed4-8b0ac78c2592
-- title:
--   P2 M Global Theory Hecke Two C norm G  1a9e454f2caf: P2 M Global Theory Hecke Two C norm G  1a9e454f2caf
-- statement:
--   The P2 M Global Theory Hecke Two C norm G  1a9e454f2caf construction uses the P2 M Global Theory Hecke Two C norm G  1a9e454f2caf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckePhiFourierConstantAtZeroDifferentiableOn.lean#L58-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckePhiFourierConstantAtZeroDifferentiableOn.lean#L58-L61

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckePhiFourierConstantAtZeroDifferentiableOn
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
open GlobalTheory GlobalTheory.HeckeTwoC
open MeasureTheory

theorem P2M_GlobalTheory_HeckeTwoC_norm_G__1a9e454f2caf (σ : ℂ) (t : ℝ) : ‖G' σ t‖ = Real.exp (-(2 + 2 * σ.re) * lg t) * (2 * lg t) := by sorry

alias «GlobalTheory».«HeckeTwoC».«norm_G'» := P2M_GlobalTheory_HeckeTwoC_norm_G__1a9e454f2caf
