-- Prove2me | Theorems.Thm_PI_EF_Lent_disc_bound
-- name    : PI.EF.Lent_disc_bound
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:29:05.55457+00:00
-- url     : https://prove2.me/theorems/7d716a6a-0274-469b-89fa-5e3f975a528c
-- title:
--   EF: Lent disc bound
-- statement:
--   The EF construction uses the Lent disc bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/HalfLeNormLentCtr.lean#L166-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/HalfLeNormLentCtr.lean#L166-L185

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LStructC
import Definitions.Def_Formalism_PeriodIntegrals_ZerosWindowIn
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_HalfLeNormLentCtr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.EF
open Complex Metric Filter Topology Set DirichletCharacter
variable {N : ℕ} [NeZero N]

theorem PI.EF.Lent_disc_bound {A C : ℝ} (hA : 0 < A) (hC : 0 < C) (hG : LGrowth A C) (hI : PI.LInvRight)
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (t : ℝ) :
    ∀ z ∈ closedBall (ctr t) 6, ‖Lent χ z‖ ≤ Real.exp (Mfun A C N t) * ‖Lent χ (ctr t)‖ := by sorry
