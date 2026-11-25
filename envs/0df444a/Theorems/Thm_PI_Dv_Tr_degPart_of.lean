-- Prove2me | Theorems.Thm_PI_Dv_Tr_degPart_of
-- name    : PI.Dv.Tr.degPart_of
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:28:30.294802+00:00
-- url     : https://prove2.me/theorems/78141c20-f3fd-468d-8778-420f3d8d1a3a
-- title:
--   Tr: deg Part of
-- statement:
--   The Tr construction uses the deg Part of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IdempotentTransfer/DegTop.lean#L25-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IdempotentTransfer/DegTop.lean#L25-L43

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DivisionRowsRationalLattice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_TraceFormulaOfRankDegree
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_DegTop
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.Tr
open PI.Dv

theorem PI.Dv.Tr.degPart_of (h1 : SplitBound) (h2 : PerSBound) : DegPart := by sorry
