-- Prove2me | Theorems.Thm_P2M_Formalism_L2_Th1_D_KernelCokernelKilling_integral_X__2606e57c7606
-- name    : P2M_Formalism_L2_Th1_D_KernelCokernelKilling_integral_X__2606e57c7606
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T21:44:34.520855+00:00
-- url     : https://prove2.me/theorems/41fee5d7-7f38-4ba8-9abe-6cdfbf00e5d0
-- title:
--   P2 M Formalism L2 Th1 D Kernel Cokernel Killing integral X  2606e57c7606: P2 M Formalism L2 Th1 D Kernel Cokernel Killing integral X  2606e57c7606
-- statement:
--   The P2 M Formalism L2 Th1 D Kernel Cokernel Killing integral X  2606e57c7606 construction uses the P2 M Formalism L2 Th1 D Kernel Cokernel Killing integral X  2606e57c7606 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/EqZeroOfPowEqOne.lean#L155-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/EqZeroOfPowEqOne.lean#L155-L160

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_LetterShift
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_EqZeroOfPowEqOne
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_frobVar_eq_expand

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.D
open Formalism.DworkPowerSeriesWeights (Integral letterLog entLog)
open Formalism.InvariantFactorPaths.G7 (frobVar frobVar_eq_expand UnrOK)
open Formalism.L2.Th1.D.KernelCokernelKilling
open MvPowerSeries
variable {K : Type} [NormedField K] {τ : Type}

theorem P2M_Formalism_L2_Th1_D_KernelCokernelKilling_integral_X__2606e57c7606 (x : τ) : Integral (X x : MvPowerSeries τ K) := by sorry

alias «Formalism».«L2».«Th1».«D».«KernelCokernelKilling».«integral_X'» := P2M_Formalism_L2_Th1_D_KernelCokernelKilling_integral_X__2606e57c7606
