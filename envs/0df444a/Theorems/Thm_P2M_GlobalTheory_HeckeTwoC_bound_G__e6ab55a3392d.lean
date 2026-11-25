-- Prove2me | Theorems.Thm_P2M_GlobalTheory_HeckeTwoC_bound_G__e6ab55a3392d
-- name    : P2M_GlobalTheory_HeckeTwoC_bound_G__e6ab55a3392d
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:05:50.577815+00:00
-- url     : https://prove2.me/theorems/b0a741e6-d8c5-4c2c-bb13-a267a6659f5a
-- title:
--   P2 M Global Theory Hecke Two C bound G  e6ab55a3392d: P2 M Global Theory Hecke Two C bound G  e6ab55a3392d
-- statement:
--   The P2 M Global Theory Hecke Two C bound G  e6ab55a3392d construction uses the P2 M Global Theory Hecke Two C bound G  e6ab55a3392d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckePhiFourierConstantAtZeroDifferentiableOn.lean#L70-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckePhiFourierConstantAtZeroDifferentiableOn.lean#L70-L90

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

theorem P2M_GlobalTheory_HeckeTwoC_bound_G__e6ab55a3392d {ε : ℝ} (hε : 0 < ε) {σ : ℂ} (hσ : -1 / 2 + ε ≤ σ.re) (t : ℝ) :
    ‖G' σ t‖ ≤ 2 / ε * Real.exp (-(1 + ε) * lg t) := by sorry

alias «GlobalTheory».«HeckeTwoC».«bound_G'» := P2M_GlobalTheory_HeckeTwoC_bound_G__e6ab55a3392d
