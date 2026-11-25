-- Prove2me | Theorems.Thm_P2M_Formalism_L2_KerInert_VC_intPS_mul__929a280bcbab
-- name    : P2M_Formalism_L2_KerInert_VC_intPS_mul__929a280bcbab
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:57:39.836875+00:00
-- url     : https://prove2.me/theorems/a2eeaf6b-4760-42b8-b728-ea1a386cb2dc
-- title:
--   P2 M Formalism L2 Ker Inert VC int PS mul  929a280bcbab: P2 M Formalism L2 Ker Inert VC int PS mul  929a280bcbab
-- statement:
--   The P2 M Formalism L2 Ker Inert VC int PS mul  929a280bcbab construction uses the P2 M Formalism L2 Ker Inert VC int PS mul  929a280bcbab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/InertKernelTheory/InertCoprimeLemmas/VarChange.lean#L234-L235
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/InertKernelTheory/InertCoprimeLemmas/VarChange.lean#L234-L235

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

theorem P2M_Formalism_L2_KerInert_VC_intPS_mul__929a280bcbab {f g : K⟦X⟧} (hf : IntPS R' f) (hg : IntPS R' g) : IntPS R' (f * g) := by sorry

alias «Formalism».«L2».«KerInert».«VC».«intPS_mul'» := P2M_Formalism_L2_KerInert_VC_intPS_mul__929a280bcbab
