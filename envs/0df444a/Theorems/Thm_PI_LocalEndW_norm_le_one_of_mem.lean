-- Prove2me | Theorems.Thm_PI_LocalEndW_norm_le_one_of_mem
-- name    : PI.LocalEndW.norm_le_one_of_mem
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:35:08.826356+00:00
-- url     : https://prove2.me/theorems/e3a3d33c-6bbb-4000-b77f-2237bfd22b71
-- title:
--   Local End W: norm le one of mem
-- statement:
--   The Local End W construction uses the norm le one of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalEndomorphisms/HenselRoot.lean#L10-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalEndomorphisms/HenselRoot.lean#L10-L10

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalEndomorphisms_ValSurjective
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalEndomorphisms_HenselRoot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial Filter Topology
open PI PI.LocalEndW
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem PI.LocalEndW.norm_le_one_of_mem (a : v.adicCompletionIntegers F) : ‖(a : v.adicCompletion F)‖ ≤ 1 := by sorry
