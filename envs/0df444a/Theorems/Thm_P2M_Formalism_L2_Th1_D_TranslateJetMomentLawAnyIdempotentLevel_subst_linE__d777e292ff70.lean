-- Prove2me | Theorems.Thm_P2M_Formalism_L2_Th1_D_TranslateJetMomentLawAnyIdempotentLevel_subst_linE__d777e292ff70
-- name    : P2M_Formalism_L2_Th1_D_TranslateJetMomentLawAnyIdempotentLevel_subst_linE__d777e292ff70
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:59:03.935948+00:00
-- url     : https://prove2.me/theorems/da1660be-ab79-4c2a-96cf-4b715535444a
-- title:
--   P2 M Formalism L2 Th1 D Translate Jet Moment Law Any Idempotent Level subst lin E  d777e292ff70: P2 M Formalism L2 Th1 D Translate Jet Moment Law Any Idempotent Level subst lin E  d777e292ff70
-- statement:
--   The P2 M Formalism L2 Th1 D Translate Jet Moment Law Any Idempotent Level subst lin E  d777e292ff70 construction uses the P2 M Formalism L2 Th1 D Translate Jet Moment Law Any Idempotent Level subst lin E  d777e292ff70 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/FirstMomentIdempotentLaw.lean#L192-L197
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/FirstMomentIdempotentLaw.lean#L192-L197

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_BiextensionPointsIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_SubstFirstCoboundaryThree
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_IpNormPowSubPowLe
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_EqZeroOfPowEqOne
import Definitions.Def_Formalism_FormalGroupWitt_WeightInvariance
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_EqSingleOfDegreeEqOne
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_FirstMomentIdempotentLaw
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
open Formalism.DworkPowerSeriesWeights (Integral mvExp torus)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq UnrOK IsLawOfLog frobVar frobVar_eq_expand)
open MvPowerSeries
open Formalism.L2.Th1.D.TranslateJetMomentLawAnyIdempotentLevel
open Pair KernelCokernelKilling
variable {K : Type} [Field K] {d : ℕ} [NeZero d]
variable {ι : Type}

theorem P2M_Formalism_L2_Th1_D_TranslateJetMomentLawAnyIdempotentLevel_subst_linE__d777e292ff70 {τ : Type} (σ : K →+* K) (om oms : ι → K) (r : ι)
    {L : ZMod d → MvPowerSeries τ K} (hL : HasSubst L) :
    subst L (linE σ (oms r)) = ∑ s : ZMod d, C (pXY σ om oms (false, r) s) * L s := by sorry

alias «Formalism».«L2».«Th1».«D».«TranslateJetMomentLawAnyIdempotentLevel».«subst_linE'» := P2M_Formalism_L2_Th1_D_TranslateJetMomentLawAnyIdempotentLevel_subst_linE__d777e292ff70
