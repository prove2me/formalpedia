-- Prove2me | Theorems.Thm_PIW_HCFdeg_commute_star
-- name    : PIW.HCFdeg.commute_star
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:48:28.913213+00:00
-- url     : https://prove2.me/theorems/dd6f20f3-ac31-5e10-9721-8428ffc4cdef
-- title:
--   HCFdeg: commute star
-- statement:
--   The HCFdeg construction uses the commute star property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalDegreeSquareIntegrable/CommuteStar.lean#L28-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalDegreeSquareIntegrable/CommuteStar.lean#L28-L38

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalDegreeSquareIntegrable_FormalDegreeFromOrthogonality
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalDegreeSquareIntegrable_CommuteStar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PIW PIW.HCFdeg
open scoped InnerProductSpace ComplexStarModule
open ContinuousLinearMap
variable {G H : Type} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (π : G →* (H →L[ℂ] H))

theorem PIW.HCFdeg.commute_star (hπ : ∀ g v, ‖π g v‖ = ‖v‖) (T : H →L[ℂ] H) (hT : ∀ g, Commute T (π g))
    (g : G) : Commute (star T) (π g) := by sorry
