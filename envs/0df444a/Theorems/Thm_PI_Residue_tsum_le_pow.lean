-- Prove2me | Theorems.Thm_PI_Residue_tsum_le_pow
-- name    : PI.Residue.tsum_le_pow
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:19:51.064901+00:00
-- url     : https://prove2.me/theorems/39e24fcf-4242-4dbb-80f5-bb724e390366
-- title:
--   Residue: tsum le pow
-- statement:
--   The Residue construction uses the tsum le pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ResidueLatticeCount/FactorizationMultisetProd.lean#L99-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ResidueLatticeCount/FactorizationMultisetProd.lean#L99-L104

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_FactorizationMultisetProd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.Residue
open scoped ENNReal

theorem PI.Residue.tsum_le_pow {β : Type*} {m : ℕ} (n : β → Fin m → ℕ) (hinj : Function.Injective n)
    (w : ℕ → ℝ≥0∞) (W : β → ℝ≥0∞) (hw : ∀ b, W b = ∏ i, w (n b i)) :
    ∑' b, W b ≤ (∑' k, w k) ^ m := by sorry
