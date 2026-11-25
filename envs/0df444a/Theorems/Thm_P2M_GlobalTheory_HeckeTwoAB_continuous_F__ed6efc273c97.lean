-- Prove2me | Theorems.Thm_P2M_GlobalTheory_HeckeTwoAB_continuous_F__ed6efc273c97
-- name    : P2M_GlobalTheory_HeckeTwoAB_continuous_F__ed6efc273c97
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:05:59.74726+00:00
-- url     : https://prove2.me/theorems/a79713c3-18ae-4c42-ae22-57623cbf496f
-- title:
--   P2 M Global Theory Hecke Two AB continuous F  ed6efc273c97: P2 M Global Theory Hecke Two AB continuous F  ed6efc273c97
-- statement:
--   The P2 M Global Theory Hecke Two AB continuous F  ed6efc273c97 construction uses the P2 M Global Theory Hecke Two AB continuous F  ed6efc273c97 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckeHankelTransformABDifferentiableOnSigma.lean#L152-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckeHankelTransformABDifferentiableOnSigma.lean#L152-L155

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

theorem P2M_GlobalTheory_HeckeTwoAB_continuous_F__ed6efc273c97 (a b : ℕ) (ν : ℝ) {y : ℝ} (hy : y ≠ 0) (σ : ℂ) : Continuous (F' a b ν y σ) := by sorry

alias «GlobalTheory».«HeckeTwoAB».«continuous_F'» := P2M_GlobalTheory_HeckeTwoAB_continuous_F__ed6efc273c97
