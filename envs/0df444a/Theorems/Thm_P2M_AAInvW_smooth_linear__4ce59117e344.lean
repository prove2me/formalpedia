-- Prove2me | Theorems.Thm_P2M_AAInvW_smooth_linear__4ce59117e344
-- name    : P2M_AAInvW_smooth_linear__4ce59117e344
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T15:50:36.352352+00:00
-- url     : https://prove2.me/theorems/ea7f28d0-d1d1-4bb1-86ce-8addbf0f4b40
-- title:
--   P2 M AAInv W smooth linear  4ce59117e344: P2 M AAInv W smooth linear  4ce59117e344
-- statement:
--   The P2 M AAInv W smooth linear  4ce59117e344 construction uses the P2 M AAInv W smooth linear  4ce59117e344 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdjointInverseTranslate/SmoothLinear.lean#L34-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdjointInverseTranslate/SmoothLinear.lean#L34-L44

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_AnaHpartUnique
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_SmoothLinear
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ContDiff
noncomputable section
open AAInvW
open Formalism.REAL Formalism.QuantumDeterminants
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem P2M_AAInvW_smooth_linear__4ce59117e344 : SmoothLin := by sorry

alias «AAInvW».«smooth_linear'» := P2M_AAInvW_smooth_linear__4ce59117e344
