-- Prove2me | Theorems.Thm_P2M_PI_Dv_IdxW_ideal_localized__4df3c3d4c027
-- name    : P2M_PI_Dv_IdxW_ideal_localized__4df3c3d4c027
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T09:39:45.328453+00:00
-- url     : https://prove2.me/theorems/b499a5f1-7bdd-5cd6-86bd-5a76ffeb809a
-- title:
--   P2 M PI Dv Idx W ideal localized  4df3c3d4c027: P2 M PI Dv Idx W ideal localized  4df3c3d4c027
-- statement:
--   The P2 M PI Dv Idx W ideal localized  4df3c3d4c027 construction uses the P2 M PI Dv Idx W ideal localized  4df3c3d4c027 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IndexCalculation/SmulMemSpanSmul.lean#L21-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IndexCalculation/SmulMemSpanSmul.lean#L21-L24

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_IdxCalc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IndexCalculation_IsLocalizedModuleToSpan
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IndexCalculation_SmulMemSpanSmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.IdxW
open NumberField IsDedekindDomain Module
variable {R : Type*} [CommRing R] {V : Type*} [AddCommGroup V] [Module R V]

theorem P2M_PI_Dv_IdxW_ideal_localized__4df3c3d4c027 (S : Submonoid R) (I : Ideal R) :
    I.localized' (Localization S) S (Algebra.linearMap R (Localization S)) =
      I.map (algebraMap R (Localization S)) := by sorry

alias «PI».«Dv».«IdxW».«ideal_localized'» := P2M_PI_Dv_IdxW_ideal_localized__4df3c3d4c027
