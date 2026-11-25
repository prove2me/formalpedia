-- Prove2me | Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_star_hs
-- name    : PI.QuotSetU.UnitaryGroupMassFormula.star_hs
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:19:20.511281+00:00
-- url     : https://prove2.me/theorems/c07fbdea-e1a0-4134-9cc0-0eb43cbb8dc2
-- title:
--   Unitary Group Mass Formula: star hs
-- statement:
--   The Unitary Group Mass Formula construction uses the star hs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryQuotientCompactness/MaximalCompactIsCompact.lean#L80-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryQuotientCompactness/MaximalCompactIsCompact.lean#L80-L82

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_SsetGroup
import Mathlib.Analysis.CStarAlgebra.Matrix
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_MaximalCompactIsCompact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
noncomputable section
open PI PI.QuotSetU PI.QuotSetU.UnitaryGroupMassFormula
open PI PI.QuotSetU

theorem PI.QuotSetU.UnitaryGroupMassFormula.star_hs (k r : ℕ) (i : Fin (2 * r + k + 1)) : star (hs k r i) = hs k r i := by sorry
