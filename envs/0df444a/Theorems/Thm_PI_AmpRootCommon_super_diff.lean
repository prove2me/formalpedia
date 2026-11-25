-- Prove2me | Theorems.Thm_PI_AmpRootCommon_super_diff
-- name    : PI.AmpRootCommon.super_diff
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:23:19.458822+00:00
-- url     : https://prove2.me/theorems/8a574bea-8e46-46ce-b7b6-984be610222e
-- title:
--   Amp Root Common: super diff
-- statement:
--   The Amp Root Common construction uses the super diff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RootSubgroupBasics/SuperdiagPairingAdjacent.lean#L120-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RootSubgroupBasics/SuperdiagPairingAdjacent.lean#L120-L131

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

theorem PI.AmpRootCommon.super_diff (hσ : ∀ i, σ (σ i) = i) (hZ : ∀ i j, Z i j = if j = σ i then ζ i else 0)
    (hζ : ∀ i, ζ i ≠ 0) (hu : u.BlockTriangular id) (hud : ∀ i, u i i = 1)
    (hu' : u'.BlockTriangular id) (hud' : ∀ i, u' i i = 1) (hrel : uᴴ * Z * u' = Z)
    (i i1 : Fin n) (hlt : (σ i).val < (σ i1).val) : u' i i1 = 0 ∧ u i i1 = 0 := by sorry
