-- Prove2me | Theorems.Thm_PI_KEX_form_single
-- name    : PI.KEX.form_single
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T13:47:04.018054+00:00
-- url     : https://prove2.me/theorems/c25c8609-01b7-41ad-a379-e4f000e6f4cc
-- title:
--   KEX: form single
-- statement:
--   The KEX construction uses the form single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/KoszulExactness/KernelExtensionOfKoszulLoweringImageLeviWeight.lean#L16-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/KoszulExactness/KernelExtensionOfKoszulLoweringImageLeviWeight.lean#L16-L17

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_KoszulExact
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_KoszulExactness_Ii
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_KoszulExactness_KoszulImageInIdeal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_KoszulExactness_KernelExtensionOfKoszulLoweringImageLeviWeight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open PI PI.KEX
open PI.KoszulExact
variable {R : Type u} [CommRing R] {D : ℕ}

theorem PI.KEX.form_single (s : Fin D → R) (k : Fin D) : form s (Pi.single k 1) = s k := by sorry
