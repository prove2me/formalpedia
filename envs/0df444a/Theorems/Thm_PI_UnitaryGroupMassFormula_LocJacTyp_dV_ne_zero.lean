-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_dV_ne_zero
-- name    : PI.UnitaryGroupMassFormula.LocJacTyp.dV_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:44:20.625882+00:00
-- url     : https://prove2.me/theorems/aa1c3f2d-a27d-4e83-87e9-1870d1239f9a
-- title:
--   Loc Jac Typ: d V ne zero
-- statement:
--   The Loc Jac Typ construction uses the d V ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalJacobianType/KitAbs.lean#L68-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalJacobianType/KitAbs.lean#L68-L72

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocJacTyp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_KitAbs
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
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem PI.UnitaryGroupMassFormula.LocJacTyp.dV_ne_zero : dV v ≠ 0 := by sorry
