-- Prove2me | Theorems.Thm_P2M_Formalism_L2_KerInert_VC_derivative_C_mul__5469c3081b6c
-- name    : P2M_Formalism_L2_KerInert_VC_derivative_C_mul__5469c3081b6c
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:58:05.003807+00:00
-- url     : https://prove2.me/theorems/78a802f1-799a-4262-aa93-0fc8b204a9a8
-- title:
--   P2 M Formalism L2 Ker Inert VC derivative C mul  5469c3081b6c: P2 M Formalism L2 Ker Inert VC derivative C mul  5469c3081b6c
-- statement:
--   The P2 M Formalism L2 Ker Inert VC derivative C mul  5469c3081b6c construction uses the P2 M Formalism L2 Ker Inert VC derivative C mul  5469c3081b6c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/InertKernelTheory/InertCoprimeLemmas/VarChange.lean#L144-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/InertKernelTheory/InertCoprimeLemmas/VarChange.lean#L144-L146

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
variable {K : Type} [Field K] [CharZero K] (W : WeierstrassCurve K) (C : WeierstrassCurve.VariableChange K)

theorem P2M_Formalism_L2_KerInert_VC_derivative_C_mul__5469c3081b6c (a : K) (f : K⟦X⟧) :
    derivative K (PowerSeries.C a * f) = PowerSeries.C a * derivative K f := by sorry

alias «Formalism».«L2».«KerInert».«VC».«derivative_C_mul'» := P2M_Formalism_L2_KerInert_VC_derivative_C_mul__5469c3081b6c
