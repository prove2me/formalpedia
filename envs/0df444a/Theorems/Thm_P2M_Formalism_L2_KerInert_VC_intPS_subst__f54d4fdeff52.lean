-- Prove2me | Theorems.Thm_P2M_Formalism_L2_KerInert_VC_intPS_subst__f54d4fdeff52
-- name    : P2M_Formalism_L2_KerInert_VC_intPS_subst__f54d4fdeff52
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:57:30.465526+00:00
-- url     : https://prove2.me/theorems/f59f994e-4cb7-467b-8436-c8841dfbae8a
-- title:
--   P2 M Formalism L2 Ker Inert VC int PS subst  f54d4fdeff52: P2 M Formalism L2 Ker Inert VC int PS subst  f54d4fdeff52
-- statement:
--   The P2 M Formalism L2 Ker Inert VC int PS subst  f54d4fdeff52 construction uses the P2 M Formalism L2 Ker Inert VC int PS subst  f54d4fdeff52 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/InertKernelTheory/InertCoprimeLemmas/VarChange.lean#L245-L247
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/InertKernelTheory/InertCoprimeLemmas/VarChange.lean#L245-L247

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

theorem P2M_Formalism_L2_KerInert_VC_intPS_subst__f54d4fdeff52 {f a : K⟦X⟧} (hf : IntPS R' f) (ha : IntPS R' a) (ha0 : constantCoeff a = 0) :
    IntPS R' (f.subst a) := by sorry

alias «Formalism».«L2».«KerInert».«VC».«intPS_subst'» := P2M_Formalism_L2_KerInert_VC_intPS_subst__f54d4fdeff52
