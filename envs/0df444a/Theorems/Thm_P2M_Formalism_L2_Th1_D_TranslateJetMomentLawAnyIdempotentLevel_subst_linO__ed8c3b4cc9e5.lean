-- Prove2me | Theorems.Thm_P2M_Formalism_L2_Th1_D_TranslateJetMomentLawAnyIdempotentLevel_subst_linO__ed8c3b4cc9e5
-- name    : P2M_Formalism_L2_Th1_D_TranslateJetMomentLawAnyIdempotentLevel_subst_linO__ed8c3b4cc9e5
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:58:48.479612+00:00
-- url     : https://prove2.me/theorems/70529992-8de8-49a1-a629-395796de8b58
-- title:
--   P2 M Formalism L2 Th1 D Translate Jet Moment Law Any Idempotent Level subst lin O  ed8c3b4cc9e5: P2 M Formalism L2 Th1 D Translate Jet Moment Law Any Idempotent Level subst lin O  ed8c3b4cc9e5
-- statement:
--   The P2 M Formalism L2 Th1 D Translate Jet Moment Law Any Idempotent Level subst lin O  ed8c3b4cc9e5 construction uses the P2 M Formalism L2 Th1 D Translate Jet Moment Law Any Idempotent Level subst lin O  ed8c3b4cc9e5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/FirstMomentIdempotentLaw.lean#L199-L204
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/FirstMomentIdempotentLaw.lean#L199-L204

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

theorem P2M_Formalism_L2_Th1_D_TranslateJetMomentLawAnyIdempotentLevel_subst_linO__ed8c3b4cc9e5 {τ : Type} (σ : K →+* K) (om oms : ι → K) (r : ι)
    {L : ZMod d → MvPowerSeries τ K} (hL : HasSubst L) :
    subst L (linO σ (om r)) = ∑ s : ZMod d, C (pXY σ om oms (true, r) s) * L s := by sorry

alias «Formalism».«L2».«Th1».«D».«TranslateJetMomentLawAnyIdempotentLevel».«subst_linO'» := P2M_Formalism_L2_Th1_D_TranslateJetMomentLawAnyIdempotentLevel_subst_linO__ed8c3b4cc9e5
