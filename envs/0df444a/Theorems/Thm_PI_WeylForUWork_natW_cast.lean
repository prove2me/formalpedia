-- Prove2me | Theorems.Thm_PI_WeylForUWork_natW_cast
-- name    : PI.WeylForUWork.natW_cast
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:44:22.536153+00:00
-- url     : https://prove2.me/theorems/242b788f-27a0-4c67-b387-9340c044b368
-- title:
--   Weyl For UWork: nat W cast
-- statement:
--   The Weyl For UWork construction uses the nat W cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylFormulaUnitary/NatWCastReal.lean#L65-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylFormulaUnitary/NatWCastReal.lean#L65-L72

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_WeylForU
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaUnitary_NatWCastReal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WeylForUWork
open Finset PI.UpqRep Formalism.BasicNotions

theorem PI.WeylForUWork.natW_cast {N : ℕ} (lam : DomWeight N) (i : Fin N) :
    ((lam.natW i : ℕ) : ℤ) = lam.w i - lam.detShift := by sorry
