-- Prove2me | Theorems.Thm_P2M_PI_ScRefExists_GlueB_incl_nsmul__52cd2813db48
-- name    : P2M_PI_ScRefExists_GlueB_incl_nsmul__52cd2813db48
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:57:47.449227+00:00
-- url     : https://prove2.me/theorems/8d777d92-b2ed-4612-a74a-8b3cc15e8e4a
-- title:
--   P2 M PI Sc Ref Exists Glue B incl nsmul  52cd2813db48: P2 M PI Sc Ref Exists Glue B incl nsmul  52cd2813db48
-- statement:
--   The P2 M PI Sc Ref Exists Glue B incl nsmul  52cd2813db48 construction uses the P2 M PI Sc Ref Exists Glue B incl nsmul  52cd2813db48 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/HGNsmulRight.lean#L137-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/HGNsmulRight.lean#L137-L139

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

theorem P2M_PI_ScRefExists_GlueB_incl_nsmul__52cd2813db48 (m : ℕ) (x : Fin I.n → I.E) : incl I (m • x) = m • incl I x := by sorry

alias «PI».«ScRefExists».«GlueB».«incl_nsmul'» := P2M_PI_ScRefExists_GlueB_incl_nsmul__52cd2813db48
