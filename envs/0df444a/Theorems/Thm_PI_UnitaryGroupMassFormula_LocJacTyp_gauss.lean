-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_gauss
-- name    : PI.UnitaryGroupMassFormula.LocJacTyp.gauss
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:58:07.974809+00:00
-- url     : https://prove2.me/theorems/991de89e-6d61-49ff-a03b-ff35feac1b76
-- title:
--   Loc Jac Typ: gauss
-- statement:
--   The Loc Jac Typ construction uses the gauss property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalJacobianType/ExpProductSquareInv.lean#L68-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalJacobianType/ExpProductSquareInv.lean#L68-L74

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocJacTyp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_KitAbs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_ExpProductSquareInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LocJacTyp
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain PI.LocJacTyp
open scoped Classical

theorem PI.UnitaryGroupMassFormula.LocJacTyp.gauss (r : ℕ) : 2 * ∑ i : Fin (r + 1), ((i : ℕ) : ℝ) = (r : ℝ) * (r + 1) := by sorry
