-- Prove2me | Theorems.Thm_PI_AmpRootCommon_relA
-- name    : PI.AmpRootCommon.relA
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:13:02.598373+00:00
-- url     : https://prove2.me/theorems/00876b34-6f9f-45c7-8e42-16bc3a3eeda4
-- title:
--   Amp Root Common: rel A
-- statement:
--   The Amp Root Common construction uses the rel A property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RootSubgroupBasics/SuperdiagPairingAdjacent.lean#L76-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RootSubgroupBasics/SuperdiagPairingAdjacent.lean#L76-L92

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

theorem PI.AmpRootCommon.relA (hσ : ∀ i, σ (σ i) = i) (hZ : ∀ i j, Z i j = if j = σ i then ζ i else 0)
    (hu : u.BlockTriangular id) (hud : ∀ i, u i i = 1) (hrel : uᴴ * Z * u' = Z) (i j : Fin n) :
    ζ i * u' (σ i) j = star (u⁻¹ (σ j) i) * ζ (σ j) := by sorry
