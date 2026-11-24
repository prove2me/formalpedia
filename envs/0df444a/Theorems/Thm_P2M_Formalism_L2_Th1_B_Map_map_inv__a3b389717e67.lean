-- Prove2me | Theorems.Thm_P2M_Formalism_L2_Th1_B_Map_map_inv__a3b389717e67
-- name    : P2M_Formalism_L2_Th1_B_Map_map_inv__a3b389717e67
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T21:05:23.202503+00:00
-- url     : https://prove2.me/theorems/2d61cc66-fdb0-4e70-bb79-dbf4bd8bdf16
-- title:
--   P2 M Formalism L2 Th1 B Map map inv  a3b389717e67: P2 M Formalism L2 Th1 B Map map inv  a3b389717e67
-- statement:
--   The P2 M Formalism L2 Th1 B Map map inv  a3b389717e67 construction uses the P2 M Formalism L2 Th1 B Map map inv  a3b389717e67 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/BaseChangeCompatible.lean#L69-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/BaseChangeCompatible.lean#L69-L73

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

theorem P2M_Formalism_L2_Th1_B_Map_map_inv__a3b389717e67 {f : PowerSeries K} (hf : PowerSeries.constantCoeff f ≠ 0) :
    PowerSeries.map j f⁻¹ = (PowerSeries.map j f)⁻¹ := by sorry

alias «Formalism».«L2».«Th1».«B».«Map».«map_inv'» := P2M_Formalism_L2_Th1_B_Map_map_inv__a3b389717e67
