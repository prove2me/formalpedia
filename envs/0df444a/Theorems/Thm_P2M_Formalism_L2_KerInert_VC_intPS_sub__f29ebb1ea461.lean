-- Prove2me | Theorems.Thm_P2M_Formalism_L2_KerInert_VC_intPS_sub__f29ebb1ea461
-- name    : P2M_Formalism_L2_KerInert_VC_intPS_sub__f29ebb1ea461
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:57:49.082805+00:00
-- url     : https://prove2.me/theorems/c10be05c-7e47-4055-87a0-bf71e5966761
-- title:
--   P2 M Formalism L2 Ker Inert VC int PS sub  f29ebb1ea461: P2 M Formalism L2 Ker Inert VC int PS sub  f29ebb1ea461
-- statement:
--   The P2 M Formalism L2 Ker Inert VC int PS sub  f29ebb1ea461 construction uses the P2 M Formalism L2 Ker Inert VC int PS sub  f29ebb1ea461 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/InertKernelTheory/InertCoprimeLemmas/VarChange.lean#L231-L232
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/InertKernelTheory/InertCoprimeLemmas/VarChange.lean#L231-L232

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

theorem P2M_Formalism_L2_KerInert_VC_intPS_sub__f29ebb1ea461 {f g : K⟦X⟧} (hf : IntPS R' f) (hg : IntPS R' g) : IntPS R' (f - g) := by sorry

alias «Formalism».«L2».«KerInert».«VC».«intPS_sub'» := P2M_Formalism_L2_KerInert_VC_intPS_sub__f29ebb1ea461
