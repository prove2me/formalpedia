-- Prove2me | Theorems.Thm_PI_ScRefExists_GlueB_mem_L_of
-- name    : PI.ScRefExists.GlueB.mem_L_of
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:26:32.9243+00:00
-- url     : https://prove2.me/theorems/82b5bebf-6175-5655-93f6-8ee22ca398fe
-- title:
--   Glue B: mem L of
-- statement:
--   The Glue B construction uses the mem L of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/HGNsmulRight.lean#L101-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/HGNsmulRight.lean#L101-L135

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

theorem PI.ScRefExists.GlueB.mem_L_of (h3 : LocGlob) {x : Fin I.n → I.E} (hx : incl I x ∈ I.Lf) : x ∈ I.L := by sorry
