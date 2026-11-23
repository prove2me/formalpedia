-- Prove2me | Theorems.Thm_PI_BeDiagZp_OpsW_substOps_holds
-- name    : PI.BeDiagZp.OpsW.substOps_holds
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:40:58.692539+00:00
-- url     : https://prove2.me/theorems/333325eb-b4f6-490d-b990-09e1d7d3cd1b
-- title:
--   Ops W: subst Ops holds
-- statement:
--   The Ops W construction uses the subst Ops holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DiagonalPadicSubstitution/SubstOpsHolds.lean#L19-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DiagonalPadicSubstitution/SubstOpsHolds.lean#L19-L45

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_SubstOps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_SubstOpsHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
open PI PI.BeDiagZp PI.BeDiagZp.OpsW
variable {p : ℕ} [Fact p.Prime]

theorem PI.BeDiagZp.OpsW.substOps_holds : SubstOps := by sorry
