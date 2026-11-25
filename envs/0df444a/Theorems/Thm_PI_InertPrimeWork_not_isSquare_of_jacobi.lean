-- Prove2me | Theorems.Thm_PI_InertPrimeWork_not_isSquare_of_jacobi
-- name    : PI.InertPrimeWork.not_isSquare_of_jacobi
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:07:11.066187+00:00
-- url     : https://prove2.me/theorems/7b000c06-a562-5594-bc68-27f07c383a34
-- title:
--   Inert Prime Work: not is Square of jacobi
-- statement:
--   The Inert Prime Work construction uses the not is Square of jacobi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertPrimeJacobi/NotIsSquareOfJacobi.lean#L8-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertPrimeJacobi/NotIsSquareOfJacobi.lean#L8-L12

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_InertPrime
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertPrimeJacobi_NotIsSquareOfJacobi
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open PI PI.InertPrimeWork

theorem PI.InertPrimeWork.not_isSquare_of_jacobi {d p : ℕ} (hp : p.Prime) (h : jacobiSym (-(d : ℤ)) p = -1) :
    ¬ IsSquare (((-(d : ℤ) : ℤ)) : ZMod p) := by sorry
