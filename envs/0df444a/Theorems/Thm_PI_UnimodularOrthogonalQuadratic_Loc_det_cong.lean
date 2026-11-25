-- Prove2me | Theorems.Thm_PI_UnimodularOrthogonalQuadratic_Loc_det_cong
-- name    : PI.UnimodularOrthogonalQuadratic.Loc.det_cong
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:30:07.734254+00:00
-- url     : https://prove2.me/theorems/45a88e38-2a2d-544b-8136-cbe6ab344f9f
-- title:
--   Loc: det cong
-- statement:
--   The Loc construction uses the det cong property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularOrthogonal/LocalOrthogonalMatrixOddPrime.lean#L47-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularOrthogonal/LocalOrthogonalMatrixOddPrime.lean#L47-L50

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

theorem PI.UnimodularOrthogonalQuadratic.Loc.det_cong {n : ℕ} {P H : Matrix (Fin n) (Fin n) S} (hP : IsUnit P.det) (hH : IsUnit H.det) :
    IsUnit (P * H * Pᴴ).det := by sorry
