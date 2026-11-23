-- Prove2me | Theorems.Thm_PI_AmpRootCommon_Z_col
-- name    : PI.AmpRootCommon.Z_col
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:13:02.441541+00:00
-- url     : https://prove2.me/theorems/19e571db-d945-4b0e-a4f7-df72ebdefb12
-- title:
--   Amp Root Common: Z col
-- statement:
--   The Amp Root Common construction uses the Z col property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RootSubgroupBasics/SuperdiagPairingAdjacent.lean#L65-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RootSubgroupBasics/SuperdiagPairingAdjacent.lean#L65-L67

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RootSubgroupBasics_SuperdiagPairingAdjacent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.AmpRootCommon
variable {n : ℕ}
variable {Z u u' : Matrix (Fin n) (Fin n) ℂ} {σ : Fin n → Fin n} {ζ : Fin n → ℂ}

theorem PI.AmpRootCommon.Z_col (hσ : ∀ i, σ (σ i) = i) (hZ : ∀ i j, Z i j = if j = σ i then ζ i else 0) (a j : Fin n)
    (ha : a ≠ σ j) : Z a j = 0 := by sorry
