-- Prove2me | Theorems.Thm_PI_ScRefExists_GlueB_hG_nsmul_left
-- name    : PI.ScRefExists.GlueB.hG_nsmul_left
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:23:06.274264+00:00
-- url     : https://prove2.me/theorems/012a0ff8-75bc-450f-909b-bd79fb4207df
-- title:
--   Glue B: h G nsmul left
-- statement:
--   The Glue B construction uses the h G nsmul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/HGNsmulRight.lean#L79-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/HGNsmulRight.lean#L79-L83

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScRefExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_HANegRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_HypsNonvacuous
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_HGNsmulRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Formalism.MainNotions.S
open scoped TensorProduct
open PI PI.ScRefExists PI.ScRefExists.GlueB
open PI.ScRefExists PI.ScRefExists.GlueA PI.ScRefExists.Sk
variable (I : Formalism.MainNotions.S.AutInst) (g : ℕ)

theorem PI.ScRefExists.GlueB.hG_nsmul_left (m : ℕ) (x y : Fin I.n → I.E) :
    Formalism.UG.hform (starRingEnd I.E) I.J (m • x) y = (m : I.E) * Formalism.UG.hform (starRingEnd I.E) I.J x y := by sorry
