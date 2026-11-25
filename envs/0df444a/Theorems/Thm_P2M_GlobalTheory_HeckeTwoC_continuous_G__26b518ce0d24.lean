-- Prove2me | Theorems.Thm_P2M_GlobalTheory_HeckeTwoC_continuous_G__26b518ce0d24
-- name    : P2M_GlobalTheory_HeckeTwoC_continuous_G__26b518ce0d24
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T00:05:52.815329+00:00
-- url     : https://prove2.me/theorems/e0b6095a-33e0-4f52-8aee-ed581936d99f
-- title:
--   P2 M Global Theory Hecke Two C continuous G  26b518ce0d24: P2 M Global Theory Hecke Two C continuous G  26b518ce0d24
-- statement:
--   The P2 M Global Theory Hecke Two C continuous G  26b518ce0d24 construction uses the P2 M Global Theory Hecke Two C continuous G  26b518ce0d24 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckePhiFourierConstantAtZeroDifferentiableOn.lean#L112-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckePhiFourierConstantAtZeroDifferentiableOn.lean#L112-L115

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

theorem P2M_GlobalTheory_HeckeTwoC_continuous_G__26b518ce0d24 (σ : ℂ) : Continuous (G' σ) := by sorry

alias «GlobalTheory».«HeckeTwoC».«continuous_G'» := P2M_GlobalTheory_HeckeTwoC_continuous_G__26b518ce0d24
