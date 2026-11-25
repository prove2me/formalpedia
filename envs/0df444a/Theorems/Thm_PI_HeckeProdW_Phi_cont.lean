-- Prove2me | Theorems.Thm_PI_HeckeProdW_Phi_cont
-- name    : PI.HeckeProdW.Phi_cont
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:31:17.87212+00:00
-- url     : https://prove2.me/theorems/25e21dc3-1ac1-463e-9d67-2ee7317e4445
-- title:
--   Hecke Prod W: Phi cont
-- statement:
--   The Hecke Prod W construction uses the Phi cont property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HeckeLocalProduct/Kernel.lean#L35-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HeckeLocalProduct/Kernel.lean#L35-L38

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_Lemmata_MiscLemmasM_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HeckeLocalProduct_Kernel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host RestrictedProduct Topology
open PI PI.HeckeProdW
variable (L : Type) [Field L] [NumberField L]

theorem PI.HeckeProdW.Phi_cont : Continuous (Phi L) := by sorry
