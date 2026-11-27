-- Prove2me | Theorems.Thm_PI_UnfoldEquiv_UnitaryGroupMassFormula_inX_apply
-- name    : PI.UnfoldEquiv.UnitaryGroupMassFormula.inX_apply
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T13:48:03.44643+00:00
-- url     : https://prove2.me/theorems/fe852a8b-dbc2-4eb7-ae53-bb23e5796cc1
-- title:
--   Unitary Group Mass Formula: in X apply
-- statement:
--   The Unitary Group Mass Formula construction uses the in X apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnfoldingEquivalence/ExtractFreeFillMatrix.lean#L16-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnfoldingEquivalence/ExtractFreeFillMatrix.lean#L16-L21

import Definitions.Def_Formalism_PeriodIntegrals_UnfoldEquiv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnfoldingEquivalence_ExtractFreeFillMatrix
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI.UnfoldEquiv PI.UnfoldEquiv.Loc
noncomputable section
open PI PI.UnfoldEquiv PI.UnfoldEquiv.UnitaryGroupMassFormula
variable {k : Type} [CommRing k]

theorem PI.UnfoldEquiv.UnitaryGroupMassFormula.inX_apply {n c : ℕ} (x : Fin n → k) (l : Fin (n + c)) :
    inX k n c x l = if h : l.1 < n then x ⟨l.1, h⟩ else 0 := by sorry
