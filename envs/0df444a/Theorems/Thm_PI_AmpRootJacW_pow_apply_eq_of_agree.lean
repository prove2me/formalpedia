-- Prove2me | Theorems.Thm_PI_AmpRootJacW_pow_apply_eq_of_agree
-- name    : PI.AmpRootJacW.pow_apply_eq_of_agree
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:23:48.01481+00:00
-- url     : https://prove2.me/theorems/8b897fdc-ffb3-49b9-b3b5-0bf347141f97
-- title:
--   Amp Root Jac W: pow apply eq of agree
-- statement:
--   The Amp Root Jac W construction uses the pow apply eq of agree property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RootSubgroupJacobian/SUpPowEqZero.lean#L58-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RootSubgroupJacobian/SUpPowEqZero.lean#L58-L68

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RootSubgroupBasics_TriShear
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RootSubgroupJacobian_SUpPowEqZero
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
open PI PI.AmpRootJacW
variable {n : ℕ}

theorem PI.AmpRootJacW.pow_apply_eq_of_agree {V V' : Matrix (Fin n) (Fin n) ℂ} (hV : SUp V) (hV' : SUp V') (g : ℕ)
    (h : ∀ a b : Fin n, b.val < a.val + g → V a b = V' a b) (m : ℕ) (i j : Fin n)
    (hij : j.val ≤ i.val + g) : (V ^ (m + 1 + 1)) i j = (V' ^ (m + 1 + 1)) i j := by sorry
