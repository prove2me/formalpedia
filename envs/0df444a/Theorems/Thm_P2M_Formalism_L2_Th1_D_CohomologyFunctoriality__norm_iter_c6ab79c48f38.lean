-- Prove2me | Theorems.Thm_P2M_Formalism_L2_Th1_D_CohomologyFunctoriality__norm_iter_c6ab79c48f38
-- name    : P2M_Formalism_L2_Th1_D_CohomologyFunctoriality__norm_iter_c6ab79c48f38
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T06:17:44.367284+00:00
-- url     : https://prove2.me/theorems/1e62802b-49b8-4a05-8103-63b975c8f259
-- title:
--   P2 M Formalism L2 Th1 D Cohomology Functoriality  norm iter c6ab79c48f38: P2 M Formalism L2 Th1 D Cohomology Functoriality  norm iter c6ab79c48f38
-- statement:
--   The P2 M Formalism L2 Th1 D Cohomology Functoriality  norm iter c6ab79c48f38 construction uses the P2 M Formalism L2 Th1 D Cohomology Functoriality  norm iter c6ab79c48f38 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/ThetaIntegerIsSSubstitution.lean#L27-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/ThetaIntegerIsSSubstitution.lean#L27-L33

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_BiextensionHypothesesOfLevelOne
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_ThetaInZIsThetaLog
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_StatementC
import Definitions.Def_Formalism_GaussJetBounds_ThmAEntryFull
import Definitions.Def_Formalism_GaussJetBounds_OneLetterGauss
import Definitions.Def_Formalism_GaussJetBounds_ThmAGauss
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_ThetaLogIsSubst
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FinalS
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_ThetaIntegerIsSSubstitution
import Theorems.Thm_Formalism_L2_Th1_D_KernelCokernelKilling_norm_iter

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
open Formalism.DworkPowerSeriesWeights (Integral mvExp torus BHyp Unram entLog oneLog thetaZ thetaOne frameJet frameJetOne
  nablaO)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq DivAB d1 swap2 UnrOK IsLawOfLog BetaHyp OmOK lamF thetaLog sSub zLin)
open Formalism.L2.Th1.D.CohomologyFunctoriality₂

theorem P2M_Formalism_L2_Th1_D_CohomologyFunctoriality__norm_iter_c6ab79c48f38 {K0 : Type} [NormedField K0] [IsUltrametricDist K0] [CharZero K0] {l : ℕ}
    {σ : K0 →+* K0} (hU : UnrOK K0 l σ) {c : K0} (hc : ‖c‖ ≤ 1) (n : ℕ) : ‖σ^[n] c‖ ≤ 1 := by sorry

alias «Formalism».«L2».«Th1».«D».«CohomologyFunctoriality₂».«norm_iter» := P2M_Formalism_L2_Th1_D_CohomologyFunctoriality__norm_iter_c6ab79c48f38
