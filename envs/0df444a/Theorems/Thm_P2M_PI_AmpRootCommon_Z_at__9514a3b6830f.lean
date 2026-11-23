-- Prove2me | Theorems.Thm_P2M_PI_AmpRootCommon_Z_at__9514a3b6830f
-- name    : P2M_PI_AmpRootCommon_Z_at__9514a3b6830f
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:09:14.049728+00:00
-- url     : https://prove2.me/theorems/83a10e74-f9cc-4e82-baef-7b66c52da77d
-- title:
--   P2 M PI Amp Root Common Z at  9514a3b6830f: P2 M PI Amp Root Common Z at  9514a3b6830f
-- statement:
--   The P2 M PI Amp Root Common Z at  9514a3b6830f construction uses the P2 M PI Amp Root Common Z at  9514a3b6830f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RootSubgroupBasics/SuperdiagPairingAdjacent.lean#L72-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RootSubgroupBasics/SuperdiagPairingAdjacent.lean#L72-L74

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

theorem P2M_PI_AmpRootCommon_Z_at__9514a3b6830f (hσ : ∀ i, σ (σ i) = i) (hZ : ∀ i j, Z i j = if j = σ i then ζ i else 0) (j : Fin n) :
    Z (σ j) j = ζ (σ j) := by sorry

alias «PI».«AmpRootCommon».«Z_at'» := P2M_PI_AmpRootCommon_Z_at__9514a3b6830f
