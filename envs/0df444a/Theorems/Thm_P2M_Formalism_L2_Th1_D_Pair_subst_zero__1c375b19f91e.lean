-- Prove2me | Theorems.Thm_P2M_Formalism_L2_Th1_D_Pair_subst_zero__1c375b19f91e
-- name    : P2M_Formalism_L2_Th1_D_Pair_subst_zero__1c375b19f91e
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T10:24:22.290149+00:00
-- url     : https://prove2.me/theorems/41a477d0-3f2a-4797-85be-d66b53cfa46f
-- title:
--   P2 M Formalism L2 Th1 D Pair subst zero  1c375b19f91e: P2 M Formalism L2 Th1 D Pair subst zero  1c375b19f91e
-- statement:
--   The P2 M Formalism L2 Th1 D Pair subst zero  1c375b19f91e construction uses the P2 M Formalism L2 Th1 D Pair subst zero  1c375b19f91e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/SubstFirstCoboundaryThree.lean#L225-L230
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/SubstFirstCoboundaryThree.lean#L225-L230

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_LetterShift
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FinalS
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_SubstFirstCoboundaryThree
import Theorems.Thm_P2M_Formalism_G_LogP_subst_zero__b4a287294211

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
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq DivAB d1 swap2 in3 cob UnrOK IsLawOfLog SimeqRules)
open MvPowerSeries
open Formalism.L2.Th1.D.Pair
variable {K : Type} [Field K]

theorem P2M_Formalism_L2_Th1_D_Pair_subst_zero__1c375b19f91e {ι κ : Type} {φ : ι → MvPowerSeries κ K} (hφ : HasSubst φ) :
    subst φ (0 : MvPowerSeries ι K) = 0 := by sorry

alias «Formalism».«L2».«Th1».«D».«Pair».«subst_zero'» := P2M_Formalism_L2_Th1_D_Pair_subst_zero__1c375b19f91e
