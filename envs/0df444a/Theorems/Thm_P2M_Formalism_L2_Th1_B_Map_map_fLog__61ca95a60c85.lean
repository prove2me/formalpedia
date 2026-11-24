-- Prove2me | Theorems.Thm_P2M_Formalism_L2_Th1_B_Map_map_fLog__61ca95a60c85
-- name    : P2M_Formalism_L2_Th1_B_Map_map_fLog__61ca95a60c85
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:37:10.468136+00:00
-- url     : https://prove2.me/theorems/dc431371-b9e4-4472-9298-c4f1c6409b0a
-- title:
--   P2 M Formalism L2 Th1 B Map map f Log  61ca95a60c85: P2 M Formalism L2 Th1 B Map map f Log  61ca95a60c85
-- statement:
--   The P2 M Formalism L2 Th1 B Map map f Log  61ca95a60c85 construction uses the P2 M Formalism L2 Th1 B Map map f Log  61ca95a60c85 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/BaseChangeCompatible.lean#L49-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/BaseChangeCompatible.lean#L49-L51

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

theorem P2M_Formalism_L2_Th1_B_Map_map_fLog__61ca95a60c85 {a : PowerSeries K} (ha : PowerSeries.constantCoeff a = 1) :
    PowerSeries.map j (fLog a) = fLog (PowerSeries.map j a) := by sorry

alias «Formalism».«L2».«Th1».«B».«Map».«map_fLog'» := P2M_Formalism_L2_Th1_B_Map_map_fLog__61ca95a60c85
