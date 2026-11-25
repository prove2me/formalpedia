-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_absV_ne_zero
-- name    : PI.UnitaryGroupMassFormula.LocJacTyp.absV_ne_zero
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T13:48:16.646681+00:00
-- url     : https://prove2.me/theorems/267d17aa-a6a7-5cc3-b662-cde297c7f511
-- title:
--   Loc Jac Typ: abs V ne zero
-- statement:
--   The Loc Jac Typ construction uses the abs V ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalJacobianType/KitAbs.lean#L28-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalJacobianType/KitAbs.lean#L28-L28

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

theorem PI.UnitaryGroupMassFormula.LocJacTyp.absV_ne_zero {x : Fv F v} (hx : x ≠ 0) : absV v x ≠ 0 := by sorry
