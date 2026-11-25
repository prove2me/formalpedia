-- Prove2me | Theorems.Thm_PI_NormGramAtOrigin_UnitaryGroupMassFormula_hform_eq
-- name    : PI.NormGramAtOrigin.UnitaryGroupMassFormula.hform_eq
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:34:58.615494+00:00
-- url     : https://prove2.me/theorems/6161a305-6219-4e83-a4c6-b5754d56c040
-- title:
--   Unitary Group Mass Formula: hform eq
-- statement:
--   The Unitary Group Mass Formula construction uses the hform eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OrthogonalFamilyExistence/ExistsOrthFamily.lean#L14-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OrthogonalFamilyExistence/ExistsOrthFamily.lean#L14-L19

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_NormGramAtOrigin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OrthogonalFamilyExistence_ExistsOrthFamily
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.NormGramAtOrigin PI.NormGramAtOrigin.UnitaryGroupMassFormula
open Matrix
variable {E : Type} [Field E] [StarRing E] {n : ℕ}

theorem PI.NormGramAtOrigin.UnitaryGroupMassFormula.hform_eq (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    hform (starRingEnd E) J x y = ∑ j, (∑ i, starRingEnd E (x i) * J i j) * y j := by sorry
