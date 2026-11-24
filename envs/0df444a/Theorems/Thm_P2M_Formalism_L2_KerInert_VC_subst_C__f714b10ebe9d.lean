-- Prove2me | Theorems.Thm_P2M_Formalism_L2_KerInert_VC_subst_C__f714b10ebe9d
-- name    : P2M_Formalism_L2_KerInert_VC_subst_C__f714b10ebe9d
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T21:37:13.612516+00:00
-- url     : https://prove2.me/theorems/7ade1b19-e7e8-40a8-99ae-aba6e1fb7df2
-- title:
--   P2 M Formalism L2 Ker Inert VC subst C  f714b10ebe9d: P2 M Formalism L2 Ker Inert VC subst C  f714b10ebe9d
-- statement:
--   The P2 M Formalism L2 Ker Inert VC subst C  f714b10ebe9d construction uses the P2 M Formalism L2 Ker Inert VC subst C  f714b10ebe9d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/InertKernelTheory/InertCoprimeLemmas/VarChange.lean#L135-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/InertKernelTheory/InertCoprimeLemmas/VarChange.lean#L135-L136

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
variable {R : Type} [CommRing R]

theorem P2M_Formalism_L2_KerInert_VC_subst_C__f714b10ebe9d {s : R⟦X⟧} (hs0 : constantCoeff s = 0) (a : R) : (PowerSeries.C a).subst s = PowerSeries.C a := by sorry

alias «Formalism».«L2».«KerInert».«VC».«subst_C'» := P2M_Formalism_L2_KerInert_VC_subst_C__f714b10ebe9d
