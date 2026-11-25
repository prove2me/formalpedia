-- Prove2me | Theorems.Thm_PI_SwBig_BigCellGProof_Hpk_rhoB
-- name    : PI.SwBig.BigCellGProof.Hpk_rhoB
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:32:00.762731+00:00
-- url     : https://prove2.me/theorems/200c5c44-05cc-4740-b03c-f7b1954b11b7
-- title:
--   Big Cell GProof: Hpk rho B
-- statement:
--   The Big Cell GProof construction uses the Hpk rho B property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BigCellConjugation/Monomial.lean#L44-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BigCellConjugation/Monomial.lean#L44-L55

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

theorem PI.SwBig.BigCellGProof.Hpk_rhoB (k r : ℕ) (i j : Fin (2 * r + k + 1)) :
    Hpk k r (rhoB k r i) (rhoB k r j) = Hpk k r i j := by sorry
