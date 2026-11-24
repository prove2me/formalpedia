-- Prove2me | Theorems.Thm_PI_GreenLabelMapW_root_pow_card
-- name    : PI.GreenLabelMapW.root_pow_card
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:58:06.715521+00:00
-- url     : https://prove2.me/theorems/253e9130-3aae-493c-983b-c92e226273e0
-- title:
--   Green Label Map W: root pow card
-- statement:
--   The Green Label Map W construction uses the root pow card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GreenLabelCharpoly/RootPowCard.lean#L22-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GreenLabelCharpoly/RootPowCard.lean#L22-L36

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

theorem PI.GreenLabelMapW.root_pow_card {P : K[X]} (hm : P.Monic) (hi : Irreducible P) (hX : P ≠ X)
    {w : AlgebraicClosure K} (hw : aeval w P = 0) :
    w ^ (Fintype.card K ^ P.natDegree - 1) = 1 := by sorry
