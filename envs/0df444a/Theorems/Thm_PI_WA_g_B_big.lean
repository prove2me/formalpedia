-- Prove2me | Theorems.Thm_PI_WA_g_B_big
-- name    : PI.WA.g_B_big
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:43:52.339813+00:00
-- url     : https://prove2.me/theorems/60de48b2-1128-4966-95f0-4f842822862c
-- title:
--   WA: g B big
-- statement:
--   The WA construction uses the g B big property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeakApproximationDVR/BigExistenceHolds.lean#L29-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeakApproximationDVR/BigExistenceHolds.lean#L29-L49

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeakApproximationDVR_BigExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeakApproximationDVR_BigExistenceHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WA
open PI.WADVR
variable {W Q : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Q]
  [Algebra W Q] [IsFractionRing W Q] {ϖ : W}

theorem PI.WA.g_B_big (hϖ : Irreducible ϖ) {q Y : Q} (hq : q ≠ 0) (hqs : Sm Q ϖ 1 q⁻¹) (hY0 : Y ≠ 0)
    (hY : Sm Q ϖ 1 Y⁻¹) {r : ℕ} (hr : 1 ≤ r) :
    1 + q ^ r ≠ 0 ∧ Sm Q ϖ 1 (q ^ r * (1 + q ^ r)⁻¹ * Y)⁻¹ := by sorry
