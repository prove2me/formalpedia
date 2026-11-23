-- Prove2me | Theorems.Thm_P2M_Formalism_L2_Th1_B_ParE_integral_C__792a83f5671c
-- name    : P2M_Formalism_L2_Th1_B_ParE_integral_C__792a83f5671c
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:37:57.133799+00:00
-- url     : https://prove2.me/theorems/4e8c05f8-bb52-4fed-b8e0-37b97a09809c
-- title:
--   P2 M Formalism L2 Th1 B Par E integral C  792a83f5671c: P2 M Formalism L2 Th1 B Par E integral C  792a83f5671c
-- statement:
--   The P2 M Formalism L2 Th1 B Par E integral C  792a83f5671c construction uses the P2 M Formalism L2 Th1 B Par E integral C  792a83f5671c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/WeierstrassSeriesIntegral.lean#L172-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/WeierstrassSeriesIntegral.lean#L172-L178

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_OneAddMulDerivLogSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_ConstantCoeffSeriesAtVariable
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_WeierstrassSeriesIntegral
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_integral_iff_lift
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_integral_of_mul_eq_one
import Theorems.Thm_P2M_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_integral_mul__d725f3beb1b3
import Theorems.Thm_P2M_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_integral_one__f427d3a2f5d0

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.ParE
open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (Simeq at1 cob)
open Formalism.InvariantFactorPaths.G7.LogarithmEquivalence (integral_iff_lift integral_mul' integral_one' integral_of_mul_eq_one)
variable {K : Type} [NormedField K] [IsUltrametricDist K] {ι : Type}

theorem P2M_Formalism_L2_Th1_B_ParE_integral_C__792a83f5671c {c : K} (hc : ‖c‖ ≤ 1) : Integral (MvPowerSeries.C c : MvPowerSeries ι K) := by sorry

alias «Formalism».«L2».«Th1».«B».«ParE».«integral_C'» := P2M_Formalism_L2_Th1_B_ParE_integral_C__792a83f5671c
