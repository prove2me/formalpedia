-- Prove2me | Theorems.Thm_PI_LocJacOrd_W_Ar_dV_ne_zero
-- name    : PI.LocJacOrd.W.Ar.dV_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:21:43.898365+00:00
-- url     : https://prove2.me/theorems/b41094a6-c818-45a1-b133-dd403dcdad53
-- title:
--   Ar: d V ne zero
-- statement:
--   The Ar construction uses the d V ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalJacobianOrder/AbsVNeZero.lean#L58-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalJacobianOrder/AbsVNeZero.lean#L58-L62

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianOrder_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianOrder_AbsVNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LocJacOrd PI.LocJacOrd.W PI.LocJacOrd.W.Ar
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain PI.LocJacOrd
open scoped TensorProduct Classical
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem PI.LocJacOrd.W.Ar.dV_ne_zero : dV v ≠ 0 := by sorry
