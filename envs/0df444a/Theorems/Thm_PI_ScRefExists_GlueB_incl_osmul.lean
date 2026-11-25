-- Prove2me | Theorems.Thm_PI_ScRefExists_GlueB_incl_osmul
-- name    : PI.ScRefExists.GlueB.incl_osmul
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:23:10.61287+00:00
-- url     : https://prove2.me/theorems/7756a2dc-c697-4ca1-ba19-882fafc230f9
-- title:
--   Glue B: incl osmul
-- statement:
--   The Glue B construction uses the incl osmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/HGNsmulRight.lean#L94-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/HGNsmulRight.lean#L94-L99

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScRefExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_HANegRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_HypsNonvacuous
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_HGNsmulRight
import Theorems.Thm_P2M_PI_ScRefExists_GlueA_inclE_mem__77a822732bed

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

theorem PI.ScRefExists.GlueB.incl_osmul (c : 𝓞 I.E) (x : Fin I.n → I.E) :
    incl I (c • x) = (⟨Formalism.UG.inclE (F := I.F) (Af I.F) (c : I.E), inclE_mem' I c⟩ : IntAf I.F I.E) •
      incl I x := by sorry
