-- Prove2me | Theorems.Thm_PI_EF_order_Lent
-- name    : PI.EF.order_Lent
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:24:52.659043+00:00
-- url     : https://prove2.me/theorems/c4fd838d-95b6-4428-9cd7-83c419b66160
-- title:
--   EF: order Lent
-- statement:
--   The EF construction uses the order Lent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/LStructC.lean#L74-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/LStructC.lean#L74-L87

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_GoodHeightExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LStructA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LStructB
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LStructC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.EF
open Complex Filter Topology Set DirichletCharacter
variable {N : ℕ} [NeZero N]

theorem PI.EF.order_Lent (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : s ≠ 1) :
    analyticOrderNatAt (Lent χ) s = analyticOrderNatAt (LFunction χ) s := by sorry
