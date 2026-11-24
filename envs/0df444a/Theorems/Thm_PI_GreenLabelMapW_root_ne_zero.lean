-- Prove2me | Theorems.Thm_PI_GreenLabelMapW_root_ne_zero
-- name    : PI.GreenLabelMapW.root_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:16:47.733798+00:00
-- url     : https://prove2.me/theorems/0eaf1840-7128-4dd1-bd03-45676a875460
-- title:
--   Green Label Map W: root ne zero
-- statement:
--   The Green Label Map W construction uses the root ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GreenLabelCharpoly/RootPowCard.lean#L11-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GreenLabelCharpoly/RootPowCard.lean#L11-L20

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GreenLabelCharpoly_RootPowCard
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial IntermediateField
noncomputable section
open PI PI.GreenLabelMapW
variable {K : Type} [Field K] [Fintype K]

theorem PI.GreenLabelMapW.root_ne_zero {P : K[X]} (hm : P.Monic) (hi : Irreducible P) (hX : P ≠ X)
    {w : AlgebraicClosure K} (hw : aeval w P = 0) : w ≠ 0 := by sorry
