-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_InHHClassFin_hform_span_left
-- name    : PI.UnitaryGroupMassFormula.InHHClassFin.hform_span_left
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T16:12:10.049826+00:00
-- url     : https://prove2.me/theorems/a5f8fb07-88aa-46d4-b8ea-1ed70fecc9fb
-- title:
--   In HHClass Fin: hform span left
-- statement:
--   The In HHClass Fin construction uses the hform span left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianClassFiniteness/HformSumRight.lean#L50-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianClassFiniteness/HformSumRight.lean#L50-L58

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianClassFiniteness_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianClassFiniteness_HformSumRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix Formalism.UG PI.InHHClassFin
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.InHHClassFin
variable {I : Formalism.MainNotions.S.AutInst} {S : Set (Fin I.n → I.E)}

theorem PI.UnitaryGroupMassFormula.InHHClassFin.hform_span_left (σ : I.E →+* I.E) (w : Fin I.n → I.E)
    (hw : ∀ s ∈ S, hform σ I.J s w = 0) :
    ∀ u ∈ Submodule.span I.E S, hform σ I.J u w = 0 := by sorry
