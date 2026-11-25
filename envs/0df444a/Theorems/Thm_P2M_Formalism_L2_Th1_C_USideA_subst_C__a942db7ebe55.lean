-- Prove2me | Theorems.Thm_P2M_Formalism_L2_Th1_C_USideA_subst_C__a942db7ebe55
-- name    : P2M_Formalism_L2_Th1_C_USideA_subst_C__a942db7ebe55
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:57:43.742007+00:00
-- url     : https://prove2.me/theorems/27f86d9f-5906-4d20-b26e-aa93c379d259
-- title:
--   P2 M Formalism L2 Th1 C USide A subst C  a942db7ebe55: P2 M Formalism L2 Th1 C USide A subst C  a942db7ebe55
-- statement:
--   The P2 M Formalism L2 Th1 C USide A subst C  a942db7ebe55 construction uses the P2 M Formalism L2 Th1 C USide A subst C  a942db7ebe55 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/USideA.lean#L122-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/USideA.lean#L122-L124

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_VeluIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_DegreeLeOfMemAntidiagonal
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_USideA
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
open PowerSeries
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.C
open Formalism.L2.Th1.C.USideA
variable {K : Type} [Field K]

theorem P2M_Formalism_L2_Th1_C_USideA_subst_C__a942db7ebe55 (a : PowerSeries K) (c : K) :
    PowerSeries.subst a (PowerSeries.C c) = PowerSeries.C c := by sorry

alias «Formalism».«L2».«Th1».«C».«USideA».«subst_C'» := P2M_Formalism_L2_Th1_C_USideA_subst_C__a942db7ebe55
