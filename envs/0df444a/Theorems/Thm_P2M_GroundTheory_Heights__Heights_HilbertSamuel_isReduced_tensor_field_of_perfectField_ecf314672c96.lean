-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_isReduced_tensor_field_of_perfectField_ecf314672c96
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_isReduced_tensor_field_of_perfectField_ecf314672c96
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:19:13.112689+00:00
-- url     : https://prove2.me/theorems/0ea7a883-65ef-4798-bd89-e32809fa9da6
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel is Reduced tensor field of perfect Field ecf314672c96: P2 M Ground Theory Heights  Heights Hilbert Samuel is Reduced tensor field of perfect Field ec
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel is Reduced tensor field of perfect Field ecf314672c96 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel is Reduced tensor field of perfect Field ecf314672c96 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PPrimeComplexRadical.lean#L25-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PPrimeComplexRadical.lean#L25-L59

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsPrimeComplexRadical
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PPrimeComplexRadical
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial TensorProduct
noncomputable section
open scoped IntermediateField.algebraAdjoinAdjoin

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_isReduced_tensor_field_of_perfectField_ecf314672c96 (K L F : Type*) [Field K] [PerfectField K]
    [Field L] [Algebra K L] [Algebra.EssFiniteType K L] [Field F] [Algebra K F] :
    IsReduced (L ⊗[K] F) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«isReduced_tensor_field_of_perfectField» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_isReduced_tensor_field_of_perfectField_ecf314672c96
