-- Prove2me | Theorems.Thm_P2M_Formalism_L2_Th1_D_BiextensionSums_map_lgF__08bf31594570
-- name    : P2M_Formalism_L2_Th1_D_BiextensionSums_map_lgF__08bf31594570
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T22:01:29.517136+00:00
-- url     : https://prove2.me/theorems/3ba4ae3c-9a9b-418f-b149-3844345ae599
-- title:
--   P2 M Formalism L2 Th1 D Biextension Sums map lg F  08bf31594570: P2 M Formalism L2 Th1 D Biextension Sums map lg F  08bf31594570
-- statement:
--   The P2 M Formalism L2 Th1 D Biextension Sums map lg F  08bf31594570 construction uses the P2 M Formalism L2 Th1 D Biextension Sums map lg F  08bf31594570 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/BiextensionOfExpSpec.lean#L16-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/BiextensionOfExpSpec.lean#L16-L25

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

theorem P2M_Formalism_L2_Th1_D_BiextensionSums_map_lgF__08bf31594570 {K0 K : Type} [Field K0] [Field K] (l : ℕ) (j : K0 →+* K) :
    PowerSeries.map j (lgF K0 l) = lgF K l := by sorry

alias «Formalism».«L2».«Th1».«D».«BiextensionSums».«map_lgF'» := P2M_Formalism_L2_Th1_D_BiextensionSums_map_lgF__08bf31594570
