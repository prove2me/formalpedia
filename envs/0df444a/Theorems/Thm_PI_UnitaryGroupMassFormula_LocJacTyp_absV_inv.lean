-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_absV_inv
-- name    : PI.UnitaryGroupMassFormula.LocJacTyp.absV_inv
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T01:20:11.483129+00:00
-- url     : https://prove2.me/theorems/dd93b299-f4cb-4040-b389-fe0daa9c7178
-- title:
--   Loc Jac Typ: abs V inv
-- statement:
--   The Loc Jac Typ construction uses the abs V inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalJacobianType/KitAbs.lean#L53-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalJacobianType/KitAbs.lean#L53-L58

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

theorem PI.UnitaryGroupMassFormula.LocJacTyp.absV_inv (x : Fv F v) : absV v x⁻¹ = (absV v x)⁻¹ := by sorry
