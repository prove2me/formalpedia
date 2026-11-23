-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_QmBorderFull_cmul
-- name    : PI.UnitaryGroupMassFormula.QmBorderFull.cmul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:45:59.181258+00:00
-- url     : https://prove2.me/theorems/df8744b5-f1a3-4353-a568-92a91d32e258
-- title:
--   Qm Border Full: cmul
-- statement:
--   The Qm Border Full construction uses the cmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BorderMinorRotation/SkipOneEqSuccAbove.lean#L135-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BorderMinorRotation/SkipOneEqSuccAbove.lean#L135-L136

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BorderMinorRotation_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BorderMinorRotation_SkipOneEqSuccAbove
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Formalism.REAL
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.QmBorderFull
open PI

theorem PI.UnitaryGroupMassFormula.QmBorderFull.cmul {A : Type*} [Ring A] (s : ℤ) (x y : A) : x * ((s : A) * y) = (s : A) * (x * y) := by sorry
