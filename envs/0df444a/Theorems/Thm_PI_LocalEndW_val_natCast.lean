-- Prove2me | Theorems.Thm_PI_LocalEndW_val_natCast
-- name    : PI.LocalEndW.val_natCast
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:35:28.649809+00:00
-- url     : https://prove2.me/theorems/ac3fe658-2473-443d-acc6-f1f6e1ed043f
-- title:
--   Local End W: val nat Cast
-- statement:
--   The Local End W construction uses the val nat Cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalEndomorphisms/IntVal.lean#L12-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalEndomorphisms/IntVal.lean#L12-L16

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocalEnd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalEndomorphisms_ValSurjective
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalEndomorphisms_IntVal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain WithZero
open PI PI.LocalEndW
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem PI.LocalEndW.val_natCast (n : ℕ) :
    Valued.v ((n : v.adicCompletion F)) = v.intValuation (n : 𝓞 F) := by sorry
