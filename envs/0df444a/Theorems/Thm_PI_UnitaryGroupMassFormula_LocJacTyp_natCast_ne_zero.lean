-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_natCast_ne_zero
-- name    : PI.UnitaryGroupMassFormula.LocJacTyp.natCast_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:27:49.284095+00:00
-- url     : https://prove2.me/theorems/ef2f04cb-4f07-4c42-aaf4-f32705d3ff21
-- title:
--   Loc Jac Typ: nat Cast ne zero
-- statement:
--   The Loc Jac Typ construction uses the nat Cast ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalJacobianType/KitAbs.lean#L84-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalJacobianType/KitAbs.lean#L84-L89

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

theorem PI.UnitaryGroupMassFormula.LocJacTyp.natCast_ne_zero {g : ℕ} (hg : 0 < g) : (g : Fv F v) ≠ 0 := by sorry
