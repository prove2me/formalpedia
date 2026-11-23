-- Prove2me | Theorems.Thm_P2M_Formalism_L2_Th1_B_Map_map_psubst__d587dd5fe1df
-- name    : P2M_Formalism_L2_Th1_B_Map_map_psubst__d587dd5fe1df
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:07:57.645874+00:00
-- url     : https://prove2.me/theorems/727aebb2-1dc8-42af-bad5-b3e79fc62155
-- title:
--   P2 M Formalism L2 Th1 B Map map psubst  d587dd5fe1df: P2 M Formalism L2 Th1 B Map map psubst  d587dd5fe1df
-- statement:
--   The P2 M Formalism L2 Th1 B Map map psubst  d587dd5fe1df construction uses the P2 M Formalism L2 Th1 B Map map psubst  d587dd5fe1df property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/BaseChangeCompatible.lean#L28-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/BaseChangeCompatible.lean#L28-L32

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_OneAddMulDerivLogSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementC
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_BaseChangeCompatible
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.Map
open Formalism.InvariantFactorPaths.G7 (at1 cob)
variable {K K' : Type} [Field K] [CharZero K] [Field K'] [CharZero K'] (j : K →+* K')

theorem P2M_Formalism_L2_Th1_B_Map_map_psubst__d587dd5fe1df {a : PowerSeries K} (ha : PowerSeries.constantCoeff a = 0)
    (f : PowerSeries K) :
    PowerSeries.map j (PowerSeries.subst a f) =
      PowerSeries.subst (PowerSeries.map j a) (PowerSeries.map j f) := by sorry

alias «Formalism».«L2».«Th1».«B».«Map».«map_psubst'» := P2M_Formalism_L2_Th1_B_Map_map_psubst__d587dd5fe1df
