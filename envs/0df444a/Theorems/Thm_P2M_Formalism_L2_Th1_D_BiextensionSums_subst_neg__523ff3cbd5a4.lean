-- Prove2me | Theorems.Thm_P2M_Formalism_L2_Th1_D_BiextensionSums_subst_neg__523ff3cbd5a4
-- name    : P2M_Formalism_L2_Th1_D_BiextensionSums_subst_neg__523ff3cbd5a4
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T22:00:42.097663+00:00
-- url     : https://prove2.me/theorems/126cecce-1741-43fd-997b-e006068acab5
-- title:
--   P2 M Formalism L2 Th1 D Biextension Sums subst neg  523ff3cbd5a4: P2 M Formalism L2 Th1 D Biextension Sums subst neg  523ff3cbd5a4
-- statement:
--   The P2 M Formalism L2 Th1 D Biextension Sums subst neg  523ff3cbd5a4 construction uses the P2 M Formalism L2 Th1 D Biextension Sums subst neg  523ff3cbd5a4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/BiextensionOfExpSpec.lean#L47-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/BiextensionOfExpSpec.lean#L47-L49

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_BiextensionPointsOfExpSpec
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_Transfer
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_BiextensionOfExpSpec
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_mvExp_add

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
open Formalism.DworkPowerSeriesWeights (Integral mvExp torus entLog thetaZ bSum linSub idM ZV)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq UnrOK IsLawOfLog mvExp_add)
open MvPowerSeries
open Pair
open Formalism.L2.Th1.D.BiextensionSums

theorem P2M_Formalism_L2_Th1_D_BiextensionSums_subst_neg__523ff3cbd5a4 {K ι κ : Type} [Field K] {φ : ι → MvPowerSeries κ K} (hφ : HasSubst φ)
    (f : MvPowerSeries ι K) : subst φ (-f) = -subst φ f := by sorry

alias «Formalism».«L2».«Th1».«D».«BiextensionSums».«subst_neg'» := P2M_Formalism_L2_Th1_D_BiextensionSums_subst_neg__523ff3cbd5a4
