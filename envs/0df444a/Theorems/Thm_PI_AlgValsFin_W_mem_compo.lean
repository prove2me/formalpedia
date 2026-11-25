-- Prove2me | Theorems.Thm_PI_AlgValsFin_W_mem_compo
-- name    : PI.AlgValsFin.W.mem_compo
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:23:15.176424+00:00
-- url     : https://prove2.me/theorems/898cf7c6-9ff1-4eae-a712-df62593846b2
-- title:
--   W: mem compo
-- statement:
--   The W construction uses the mem compo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AlgebraicValuesFinite/IsIntegralOfMemCompo.lean#L20-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AlgebraicValuesFinite/IsIntegralOfMemCompo.lean#L20-L21

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_ClassSame
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_IsIntegralOfMemCompo
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.L2.Host
open PI PI.AlgValsFin PI.AlgValsFin.W
variable {L : Type} [Field L] [NumberField L]

theorem PI.AlgValsFin.W.mem_compo (φ : L →+* ℂ) (x : L) : φ x ∈ compo L := by sorry
