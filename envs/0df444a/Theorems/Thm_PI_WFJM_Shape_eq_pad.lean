-- Prove2me | Theorems.Thm_PI_WFJM_Shape_eq_pad
-- name    : PI.WFJM.Shape.eq_pad
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:44:15.275791+00:00
-- url     : https://prove2.me/theorems/bf28efa2-57b1-4ea4-b8d2-c55d2227f607
-- title:
--   Shape: eq pad
-- statement:
--   The Shape construction uses the eq pad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/ShapeFromFacts.lean#L137-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/ShapeFromFacts.lean#L137-L165

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_GlobalTheory
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ShapeFromFacts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action
open PI PI.WFJM PI.WFJM.Shape
open PI.FJM
variable {n : ℕ}

theorem PI.WFJM.Shape.eq_pad (f : Fin n → ℚ) (hint : ∀ i, ((⌊f i⌋ : ℤ) : ℚ) = f i)
    (hp : ∀ i i' : Fin n, i < i' → 0 < f i' → 0 < f i) (hn : ∀ i i' : Fin n, i < i' → f i < 0 → f i' < 0)
    (i : Fin n) :
    f i = (pad (lpos (αP f)) (n - (lpos (αP f)).length - (lneg (αN f)).length) (lneg (αN f))).getD i 0 := by sorry
