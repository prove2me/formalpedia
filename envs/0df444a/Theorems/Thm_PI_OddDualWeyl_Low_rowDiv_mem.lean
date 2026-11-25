-- Prove2me | Theorems.Thm_PI_OddDualWeyl_Low_rowDiv_mem
-- name    : PI.OddDualWeyl.Low.rowDiv_mem
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:13:43.485225+00:00
-- url     : https://prove2.me/theorems/2446004e-d887-4999-b995-f3db22a1f726
-- title:
--   Low: row Div mem
-- statement:
--   The Low construction uses the row Div mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/MnrUpdateEqZero.lean#L111-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/MnrUpdateEqZero.lean#L111-L120

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_MnrUpdateEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix
noncomputable section
open PI PI.OddDualWeyl PI.OddDualWeyl.Low
variable {R : Type*} [CommRing R]

theorem PI.OddDualWeyl.Low.rowDiv_mem {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) (a b : Fin r) (j : ℕ)
    {f : MvPolynomial (Fin r × Fin n) R} (hf : f ∈ weyl R r n hn ν) :
    rowDiv R a b j f ∈ weyl R r n hn ν := by sorry
