-- Prove2me | Theorems.Thm_PI_InertPrimeWork_inert
-- name    : PI.InertPrimeWork.inert
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:07:40.362831+00:00
-- url     : https://prove2.me/theorems/1e47444e-09f0-4832-bd87-e088167757d7
-- title:
--   Inert Prime Work: inert
-- statement:
--   The Inert Prime Work construction uses the inert property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertPrimeJacobi/NotIsSquareOfJacobi.lean#L14-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertPrimeJacobi/NotIsSquareOfJacobi.lean#L14-L81

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

theorem PI.InertPrimeWork.inert (K : Type) [Field K] [NumberField K] (hK : Module.finrank ℚ K = 2) (b : K) (d p : ℕ)
    (hb : b ^ 2 = -(d : K)) (hp : p.Prime) (hj : jacobiSym (-(d : ℤ)) p = -1) :
    (Ideal.span {(p : 𝓞 K)}).IsPrime := by sorry
