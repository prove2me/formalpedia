-- Prove2me | Theorems.Thm_PI_AmpRootCommon_Z_row
-- name    : PI.AmpRootCommon.Z_row
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:13:15.752639+00:00
-- url     : https://prove2.me/theorems/03c7b749-f465-47ef-8281-1f420ed0dbbe
-- title:
--   Amp Root Common: Z row
-- statement:
--   The Amp Root Common construction uses the Z row property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RootSubgroupBasics/SuperdiagPairingAdjacent.lean#L62-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RootSubgroupBasics/SuperdiagPairingAdjacent.lean#L62-L63

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

theorem PI.AmpRootCommon.Z_row (hZ : ∀ i j, Z i j = if j = σ i then ζ i else 0) (i b : Fin n) (hb : b ≠ σ i) : Z i b = 0 := by sorry
