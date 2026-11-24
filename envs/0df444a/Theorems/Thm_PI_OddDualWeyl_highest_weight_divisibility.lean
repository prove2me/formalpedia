-- Prove2me | Theorems.Thm_PI_OddDualWeyl_highest_weight_divisibility
-- name    : PI.OddDualWeyl.highest_weight_divisibility
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:50:38.233107+00:00
-- url     : https://prove2.me/theorems/5c86d2aa-bc0f-40bd-a3d4-1d9552eca932
-- title:
--   Odd Dual Weyl: highest weight divisibility
-- statement:
--   The Odd Dual Weyl construction uses the highest weight divisibility property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/HighestWeightMultiplicity.lean#L234-L241
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/HighestWeightMultiplicity.lean#L234-L241

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_HighestWeightMultiplicity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix
noncomputable section
open PI PI.OddDualWeyl
open Hom

theorem PI.OddDualWeyl.highest_weight_divisibility : MHdiv := by sorry
