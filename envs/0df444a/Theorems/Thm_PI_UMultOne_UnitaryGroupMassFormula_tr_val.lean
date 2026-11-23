-- Prove2me | Theorems.Thm_PI_UMultOne_UnitaryGroupMassFormula_tr_val
-- name    : PI.UMultOne.UnitaryGroupMassFormula.tr_val
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:57:48.410885+00:00
-- url     : https://prove2.me/theorems/1f690ce1-a252-4879-bf0e-af916c30885b
-- title:
--   Unitary Group Mass Formula: tr val
-- statement:
--   The Unitary Group Mass Formula construction uses the tr val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitarySecondCountable/Assembly.lean#L31-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitarySecondCountable/Assembly.lean#L31-L33

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UMultOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitarySecondCountable_Assembly
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UMultOne PI.UMultOne.UnitaryGroupMassFormula
open Matrix Set

theorem PI.UMultOne.UnitaryGroupMassFormula.tr_val (m : ℕ) (g : Matrix.unitaryGroup (Fin m) ℂ) :
    ((tr m g : Matrix.unitaryGroup (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ) =
      (g : Matrix (Fin m) (Fin m) ℂ)ᵀ := by sorry
