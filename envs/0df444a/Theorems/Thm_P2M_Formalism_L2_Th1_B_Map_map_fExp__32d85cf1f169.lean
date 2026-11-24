-- Prove2me | Theorems.Thm_P2M_Formalism_L2_Th1_B_Map_map_fExp__32d85cf1f169
-- name    : P2M_Formalism_L2_Th1_B_Map_map_fExp__32d85cf1f169
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:14:57.742124+00:00
-- url     : https://prove2.me/theorems/0c6cafd3-096e-405e-8826-7c9bca02220c
-- title:
--   P2 M Formalism L2 Th1 B Map map f Exp  32d85cf1f169: P2 M Formalism L2 Th1 B Map map f Exp  32d85cf1f169
-- statement:
--   The P2 M Formalism L2 Th1 B Map map f Exp  32d85cf1f169 construction uses the P2 M Formalism L2 Th1 B Map map f Exp  32d85cf1f169 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/BaseChangeCompatible.lean#L39-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/BaseChangeCompatible.lean#L39-L41

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

theorem P2M_Formalism_L2_Th1_B_Map_map_fExp__32d85cf1f169 {a : PowerSeries K} (ha : PowerSeries.constantCoeff a = 0) :
    PowerSeries.map j (fExp a) = fExp (PowerSeries.map j a) := by sorry

alias «Formalism».«L2».«Th1».«B».«Map».«map_fExp'» := P2M_Formalism_L2_Th1_B_Map_map_fExp__32d85cf1f169
