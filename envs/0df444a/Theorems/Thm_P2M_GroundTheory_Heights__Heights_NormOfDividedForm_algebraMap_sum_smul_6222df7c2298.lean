-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NormOfDividedForm_algebraMap_sum_smul_6222df7c2298
-- name    : P2M_GroundTheory_Heights__Heights_NormOfDividedForm_algebraMap_sum_smul_6222df7c2298
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:32:48.756836+00:00
-- url     : https://prove2.me/theorems/c2532dc1-1efb-4cfe-a69a-a1cc5c81ed47
-- title:
--   P2 M Ground Theory Heights  Heights Norm Of Divided Form algebra Map sum smul 6222df7c2298: P2 M Ground Theory Heights  Heights Norm Of Divided Form algebra Map sum smul 6222df7c2298
-- statement:
--   The P2 M Ground Theory Heights  Heights Norm Of Divided Form algebra Map sum smul 6222df7c2298 construction uses the P2 M Ground Theory Heights  Heights Norm Of Divided Form algebra Map sum smul 6222df7c2298 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PNormOfDividedForm.lean#L21-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PNormOfDividedForm.lean#L21-L25

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
omit [IsDomain O] [IsFractionRing O K] [IsLocalization (Algebra.algebraMapSubmonoid B O⁰) L]

theorem P2M_GroundTheory_Heights__Heights_NormOfDividedForm_algebraMap_sum_smul_6222df7c2298 {n : ℕ} (η : Fin n → B) (v : Fin n → O) :
    algebraMap B L (∑ m, v m • η m) = ∑ m, algebraMap O K (v m) • algebraMap B L (η m) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NormOfDividedForm».«algebraMap_sum_smul» := P2M_GroundTheory_Heights__Heights_NormOfDividedForm_algebraMap_sum_smul_6222df7c2298
