-- Prove2me | Theorems.Thm_PI_UG_W_hStd_apply
-- name    : PI.UG.W.hStd_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:42:24.534774+00:00
-- url     : https://prove2.me/theorems/8ea07bc0-8733-4e26-887c-e6f23e3cd1f2
-- title:
--   W: h Std apply
-- statement:
--   The W construction uses the h Std apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularGenus/StdLatEqSpan.lean#L10-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularGenus/StdLatEqSpan.lean#L10-L11

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularGenus_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularGenus_StdLatEqSpan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
open PI PI.UG PI.UG.W

theorem PI.UG.W.hStd_apply (E : Type) [Field E] [StarRing E] (n : ℕ) (x y : Sp E n) :
    hStd E n x y = ∑ i, star (x i) * y i := by sorry
