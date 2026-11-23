-- Prove2me | Theorems.Thm_PI_AmpRootJacW_sUp_pow
-- name    : PI.AmpRootJacW.sUp_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:58:03.817277+00:00
-- url     : https://prove2.me/theorems/8be950d0-a570-4907-8b9e-1d1969ff021f
-- title:
--   Amp Root Jac W: s Up pow
-- statement:
--   The Amp Root Jac W construction uses the s Up pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RootSubgroupJacobian/SUpPowEqZero.lean#L18-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RootSubgroupJacobian/SUpPowEqZero.lean#L18-L28

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

theorem PI.AmpRootJacW.sUp_pow {V : Matrix (Fin n) (Fin n) ℂ} (hV : SUp V) :
    ∀ (m : ℕ) (i j : Fin n), j.val < i.val + m → (V ^ m) i j = 0
  := by sorry
