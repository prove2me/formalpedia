-- Prove2me | Theorems.Thm_PI_Dv_GLP_card_ne_zero
-- name    : PI.Dv.GLP.card_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:45:18.807805+00:00
-- url     : https://prove2.me/theorems/aa4cba01-2499-4715-b7d8-cdcd781d6c05
-- title:
--   GLP: card ne zero
-- statement:
--   The GLP construction uses the card ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionLattices/FinrankIntertw.lean#L104-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionLattices/FinrankIntertw.lean#L104-L105

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SameFormAllLevels
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionLattices_FinrankIntertw
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.GLP
open Representation
variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]

theorem PI.Dv.GLP.card_ne_zero [CharZero K] : ((Fintype.card G : ℕ) : K) ≠ 0 := by sorry
