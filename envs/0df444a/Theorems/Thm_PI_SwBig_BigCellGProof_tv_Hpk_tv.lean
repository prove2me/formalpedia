-- Prove2me | Theorems.Thm_PI_SwBig_BigCellGProof_tv_Hpk_tv
-- name    : PI.SwBig.BigCellGProof.tv_Hpk_tv
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:31:55.307621+00:00
-- url     : https://prove2.me/theorems/bc812a56-be69-47f8-94e2-dae46f667aeb
-- title:
--   Big Cell GProof: tv Hpk tv
-- statement:
--   The Big Cell GProof construction uses the tv Hpk tv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BigCellConjugation/Monomial.lean#L57-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BigCellConjugation/Monomial.lean#L57-L85

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LongWeylElementSquare
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BigCellConjugation_Monomial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.SwBig PI.SwBig.BigCellGProof
open PI.SwBig

theorem PI.SwBig.BigCellGProof.tv_Hpk_tv (k r : ℕ) (c : Fin r → ℂ) (hc : ∀ a, c a ≠ 0) (i j : Fin (2 * r + k + 1)) :
    star (tv k r c i) * Hpk k r i j * tv k r c j = Hpk k r i j := by sorry
