-- Prove2me | Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_restriction_to_affine_surjective
-- name    : PI.TwistedEisensteinNonvanishing.W.restriction_to_affine_surjective
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:30:11.812582+00:00
-- url     : https://prove2.me/theorems/a5d2d2fc-2f6f-470f-a529-e4fc726115b3
-- title:
--   W: restriction to affine surjective
-- statement:
--   The W construction uses the restriction to affine surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedEisensteinCoset/FreeCoordinateAffineInvertible.lean#L204-L216
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedEisensteinCoset/FreeCoordinateAffineInvertible.lean#L204-L216

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_IaDivDown
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_FreeCoordinateAffineInvertible
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Module
noncomputable section
open PI PI.TwistedEisensteinNonvanishing PI.TwistedEisensteinNonvanishing.W
open Loc LocE
variable {E : Type} [Field E]

theorem PI.TwistedEisensteinNonvanishing.W.restriction_to_affine_surjective : ResXSurjP := by sorry
