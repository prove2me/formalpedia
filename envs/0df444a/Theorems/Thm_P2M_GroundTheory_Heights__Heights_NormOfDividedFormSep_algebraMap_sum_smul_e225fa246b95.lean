-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NormOfDividedFormSep_algebraMap_sum_smul_e225fa246b95
-- name    : P2M_GroundTheory_Heights__Heights_NormOfDividedFormSep_algebraMap_sum_smul_e225fa246b95
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:30:55.945491+00:00
-- url     : https://prove2.me/theorems/f8706661-2740-4d29-b726-eb0d2a84edab
-- title:
--   P2 M Ground Theory Heights  Heights Norm Of Divided Form Sep algebra Map sum smul e225fa246b95: P2 M Ground Theory Heights  Heights Norm Of Divided Form Sep algebra Map sum smul e225fa246b95
-- statement:
--   The P2 M Ground Theory Heights  Heights Norm Of Divided Form Sep algebra Map sum smul e225fa246b95 construction uses the P2 M Ground Theory Heights  Heights Norm Of Divided Form Sep algebra Map sum smul e225fa246b95 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PNormOfDividedFormSep.lean#L21-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PNormOfDividedFormSep.lean#L21-L25

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsChartNormSep
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsNormForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PNormOfDividedFormSep
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
open GroundTheory.Heights₂.Heights.NormOfDividedFormSep
variable {O B K L : Type} [CommRing O] [IsDomain O] [CommRing B] [Algebra O B] [Field K] [Field L] [Algebra O K]
  [IsFractionRing O K] [Algebra B L] [Algebra K L] [Algebra O L] [IsScalarTower O K L] [IsScalarTower O B L]
  [IsLocalization (Algebra.algebraMapSubmonoid B O⁰) L]
omit [IsDomain O] [IsFractionRing O K] [IsLocalization (Algebra.algebraMapSubmonoid B O⁰) L]

theorem P2M_GroundTheory_Heights__Heights_NormOfDividedFormSep_algebraMap_sum_smul_e225fa246b95 {n : ℕ} (η : Fin n → B) (v : Fin n → O) :
    algebraMap B L (∑ m, v m • η m) = ∑ m, algebraMap O K (v m) • algebraMap B L (η m) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NormOfDividedFormSep».«algebraMap_sum_smul» := P2M_GroundTheory_Heights__Heights_NormOfDividedFormSep_algebraMap_sum_smul_e225fa246b95
