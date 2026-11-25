-- Prove2me | Theorems.Thm_PI_ArtSch_Glue_v_l_lt_one
-- name    : PI.ArtSch.Glue.v_l_lt_one
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:23:43.176691+00:00
-- url     : https://prove2.me/theorems/5fbf577a-9177-582d-b761-aec81db597a4
-- title:
--   Glue: v l lt one
-- statement:
--   The Glue construction uses the v l lt one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ValuationGluing/ValbLeOfCoeffEqZero.lean#L18-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ValuationGluing/ValbLeOfCoeffEqZero.lean#L18-L25

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ArtSch
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ValuationGluing_ValbLeOfCoeffEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.ArtSch PI.ArtSch.Glue
open scoped NNReal
noncomputable section
variable {l : ℕ} [hl : Fact l.Prime]

theorem PI.ArtSch.Glue.v_l_lt_one : (PadicComplex.valued l).v ((l : ℕ) : PadicComplex l) < 1 := by sorry
