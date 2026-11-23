-- Prove2me | Theorems.Thm_PI_LocalEndW_isAdicComplete
-- name    : PI.LocalEndW.isAdicComplete
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:34:04.063014+00:00
-- url     : https://prove2.me/theorems/395cfd2f-7b05-4183-91aa-b18d905a4bf2
-- title:
--   Local End W: is Adic Complete
-- statement:
--   The Local End W construction uses the is Adic Complete property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalEndomorphisms/HenselRoot.lean#L21-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalEndomorphisms/HenselRoot.lean#L21-L48

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

theorem PI.LocalEndW.isAdicComplete (ϖ : v.adicCompletionIntegers F) (hϖ : ϖ ≠ 0)
    (h1 : ‖(ϖ : v.adicCompletion F)‖ < 1) :
    IsAdicComplete (Ideal.span {ϖ}) (v.adicCompletionIntegers F) := by sorry
