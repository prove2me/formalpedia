-- Prove2me | Theorems.Thm_PI_WwMinorExpandWork_repM_add
-- name    : PI.WwMinorExpandWork.repM_add
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:46:18.983801+00:00
-- url     : https://prove2.me/theorems/e69c580c-d949-559a-bb1b-1c72d6c2e8c2
-- title:
--   Ww Minor Expand Work: rep M add
-- statement:
--   The Ww Minor Expand Work construction uses the rep M add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MinorExpansion/WwMinorExpandMain.lean#L26-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MinorExpansion/WwMinorExpandMain.lean#L26-L31

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_WwMinorExpand
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonomialFrameSpan_DetSubmatrixFun
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinorExpansion_WwMinorExpandMain
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open PI PI.WwMinorExpandWork
open PI.WwMinorExpand
variable {Lt : Type} [Fintype Lt] [DecidableEq Lt] (N0 N1 : ℕ)

theorem PI.WwMinorExpandWork.repM_add (s : Lt) (p : ℕ) {x y : MvPolynomial (KM.XZ Lt N0 N1) ℤ}
    (hx : RepM N0 N1 s p x) (hy : RepM N0 N1 s p y) : RepM N0 N1 s p (x + y) := by sorry
