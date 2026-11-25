-- Prove2me | Theorems.Thm_PI_UnimodularOrthogonalQuadratic_Loc_cong_apply_self
-- name    : PI.UnimodularOrthogonalQuadratic.Loc.cong_apply_self
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:30:49.924895+00:00
-- url     : https://prove2.me/theorems/a5fb36cf-86be-5b51-a68e-b1965734debb
-- title:
--   Loc: cong apply self
-- statement:
--   The Loc construction uses the cong apply self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularOrthogonal/LocalOrthogonalMatrixOddPrime.lean#L39-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularOrthogonal/LocalOrthogonalMatrixOddPrime.lean#L39-L41

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularOrthogonal_MatOrthoLocal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularOrthogonal_LocalOrthogonalMatrixOddPrime
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnimodularOrthogonalQuadratic PI.UnimodularOrthogonalQuadratic.Loc
open Matrix
variable {S : Type} [CommRing S] [StarRing S]

theorem PI.UnimodularOrthogonalQuadratic.Loc.cong_apply_self {n : ℕ} (P H : Matrix (Fin n) (Fin n) S) (a : Fin n) :
    (P * H * Pᴴ) a a = q H (P a) := by sorry
