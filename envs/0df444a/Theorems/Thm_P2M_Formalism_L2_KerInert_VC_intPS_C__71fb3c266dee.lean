-- Prove2me | Theorems.Thm_P2M_Formalism_L2_KerInert_VC_intPS_C__71fb3c266dee
-- name    : P2M_Formalism_L2_KerInert_VC_intPS_C__71fb3c266dee
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:58:06.098082+00:00
-- url     : https://prove2.me/theorems/98e41853-f705-48f8-a289-3f8ebf83e418
-- title:
--   P2 M Formalism L2 Ker Inert VC int PS C  71fb3c266dee: P2 M Formalism L2 Ker Inert VC int PS C  71fb3c266dee
-- statement:
--   The P2 M Formalism L2 Ker Inert VC int PS C  71fb3c266dee construction uses the P2 M Formalism L2 Ker Inert VC int PS C  71fb3c266dee property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/InertKernelTheory/InertCoprimeLemmas/VarChange.lean#L222-L223
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/InertKernelTheory/InertCoprimeLemmas/VarChange.lean#L222-L223

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FlowTwoTorsionWp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Points
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_CurveEndoAll
import Definitions.Def_Formalism_LocalToGlobal_InertKernelTheory_InertCoprimeLemmas_VarChange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
noncomputable section
open Formalism Formalism.L2 Formalism.L2.KerInert Formalism.L2.KerInert.VC
open Formalism.L2.Th1.A
open Formalism.L2.Th1.C
variable {K : Type} [Field K] [CharZero K] (R' : Subring K)

theorem P2M_Formalism_L2_KerInert_VC_intPS_C__71fb3c266dee {a : K} (ha : a ∈ R') : IntPS R' (PowerSeries.C a) := by sorry

alias «Formalism».«L2».«KerInert».«VC».«intPS_C'» := P2M_Formalism_L2_KerInert_VC_intPS_C__71fb3c266dee
