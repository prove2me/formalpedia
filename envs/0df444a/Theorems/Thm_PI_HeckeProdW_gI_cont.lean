-- Prove2me | Theorems.Thm_PI_HeckeProdW_gI_cont
-- name    : PI.HeckeProdW.gI_cont
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:30:57.587725+00:00
-- url     : https://prove2.me/theorems/21d0faf2-dc14-4ee0-b365-6ab4ccc9c30c
-- title:
--   Hecke Prod W: g I cont
-- statement:
--   The Hecke Prod W construction uses the g I cont property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HeckeLocalProduct/Kernel.lean#L25-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HeckeLocalProduct/Kernel.lean#L25-L29

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

theorem PI.HeckeProdW.gI_cont : Continuous (gI L) := by sorry
