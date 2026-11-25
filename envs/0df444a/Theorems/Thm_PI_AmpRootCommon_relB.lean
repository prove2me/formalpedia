-- Prove2me | Theorems.Thm_PI_AmpRootCommon_relB
-- name    : PI.AmpRootCommon.relB
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:23:00.516818+00:00
-- url     : https://prove2.me/theorems/dab4e945-1409-5273-8024-9ed50fc314b9
-- title:
--   Amp Root Common: rel B
-- statement:
--   The Amp Root Common construction uses the rel B property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RootSubgroupBasics/SuperdiagPairingAdjacent.lean#L94-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RootSubgroupBasics/SuperdiagPairingAdjacent.lean#L94-L109

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

theorem PI.AmpRootCommon.relB (hσ : ∀ i, σ (σ i) = i) (hZ : ∀ i j, Z i j = if j = σ i then ζ i else 0)
    (hu' : u'.BlockTriangular id) (hud' : ∀ i, u' i i = 1) (hrel : uᴴ * Z * u' = Z) (i j : Fin n) :
    star (u (σ j) i) * ζ (σ j) = ζ i * u'⁻¹ (σ i) j := by sorry
