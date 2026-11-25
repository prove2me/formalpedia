-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NormOfDividedForm_adjoin_range_eq_top_642ff4789c14
-- name    : P2M_GroundTheory_Heights__Heights_NormOfDividedForm_adjoin_range_eq_top_642ff4789c14
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:04:47.912042+00:00
-- url     : https://prove2.me/theorems/2e2e0f80-ec46-4e99-8509-be66bc6348f2
-- title:
--   P2 M Ground Theory Heights  Heights Norm Of Divided Form adjoin range eq top 642ff4789c14: P2 M Ground Theory Heights  Heights Norm Of Divided Form adjoin range eq top 642ff4789c14
-- statement:
--   The P2 M Ground Theory Heights  Heights Norm Of Divided Form adjoin range eq top 642ff4789c14 construction uses the P2 M Ground Theory Heights  Heights Norm Of Divided Form adjoin range eq top 642ff4789c14 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PNormOfDividedForm.lean#L27-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PNormOfDividedForm.lean#L27-L49

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsNormOfDividedForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsNormForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PNormOfDividedForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
open scoped nonZeroDivisors
noncomputable section
open GroundTheory.Heights₂.Heights.NormOfDividedForm
variable {O B K L : Type} [CommRing O] [IsDomain O] [CommRing B] [Algebra O B] [Field K] [Field L] [Algebra O K]
  [IsFractionRing O K] [Algebra B L] [Algebra K L] [Algebra O L] [IsScalarTower O K L] [IsScalarTower O B L]
  [IsLocalization (Algebra.algebraMapSubmonoid B O⁰) L]

theorem P2M_GroundTheory_Heights__Heights_NormOfDividedForm_adjoin_range_eq_top_642ff4789c14 {n : ℕ} (η : Fin n → B) (hgen : Algebra.adjoin O (Set.range η) = ⊤) :
    Algebra.adjoin K (Set.range fun m => algebraMap B L (η m)) = ⊤ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NormOfDividedForm».«adjoin_range_eq_top» := P2M_GroundTheory_Heights__Heights_NormOfDividedForm_adjoin_range_eq_top_642ff4789c14
