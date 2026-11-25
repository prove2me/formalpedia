-- Prove2me | Theorems.Thm_PI_VolStabSW_FFHS_card_norm
-- name    : PI.VolStabSW.FFHS.card_norm
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:41:20.421067+00:00
-- url     : https://prove2.me/theorems/30d476bd-71aa-4f02-818d-5d00bc1a8387
-- title:
--   FFHS: card norm
-- statement:
--   The FFHS construction uses the card norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/LocDensFFCnt.lean#L51-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/LocDensFFCnt.lean#L51-L144

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensFFHS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensFFCnt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW PI.VolStabSW.FFHS
open Module
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {σ : K →+* K}

theorem PI.VolStabSW.FFHS.card_norm (q : ℕ) (hq0 : 0 < q) (hK : Fintype.card K = q ^ 2) (hσ : ∀ x, σ (σ x) = x)
    (h2 : (2 : K) ≠ 0)
    (hN : ∀ d, σ d = d → Nat.card {t : K // t * σ t = d} = if d = 0 then 1 else q + 1) :
    ∀ (m : ℕ) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V]
      (h : V → V → K), IsHS σ h → finrank K V = m → ∀ c, σ c = c →
      (Nat.card {x : V // h x x = c} : ℝ) = (q : ℝ) ^ (2 * (m : ℤ) - 1) +
        (-1) ^ m * (q : ℝ) ^ ((m : ℤ) - 1) * ((if c = 0 then (q : ℝ) else 0) - 1) := by sorry
