-- Prove2me | Theorems.Thm_PI_AmpRootCommon_sum_super
-- name    : PI.AmpRootCommon.sum_super
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:08:19.876868+00:00
-- url     : https://prove2.me/theorems/f26a86ba-1205-4e50-97e4-977c8170ebea
-- title:
--   Amp Root Common: sum super
-- statement:
--   The Amp Root Common construction uses the sum super property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RootSubgroupBasics/SuperdiagPairingAdjacent.lean#L171-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RootSubgroupBasics/SuperdiagPairingAdjacent.lean#L171-L191

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
variable {m : ℕ}

theorem PI.AmpRootCommon.sum_super {Z u u' : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ} {σ : Fin (m + 1) → Fin (m + 1)}
    {ζ : Fin (m + 1) → ℂ} (hσ : ∀ i, σ (σ i) = i) (hZ : ∀ i j, Z i j = if j = σ i then ζ i else 0)
    (hζ : ∀ i, ζ i ≠ 0)
    (hadj : ∀ i i1 : Fin (m + 1), i1.val = i.val + 1 →
      ((σ i1).val + 1 = (σ i).val ∧ ζ (σ i1) = - ζ (σ i)) ∨ (σ i).val < (σ i1).val)
    (hu : u.BlockTriangular id) (hud : ∀ i, u i i = 1)
    (hu' : u'.BlockTriangular id) (hud' : ∀ i, u' i i = 1) (hrel : uᴴ * Z * u' = Z) :
    ∑ i : Fin m, u' i.castSucc i.succ = star (∑ i : Fin m, u i.castSucc i.succ) := by sorry
