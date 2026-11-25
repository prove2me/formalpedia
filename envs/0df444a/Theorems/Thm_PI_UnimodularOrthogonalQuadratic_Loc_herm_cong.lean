-- Prove2me | Theorems.Thm_PI_UnimodularOrthogonalQuadratic_Loc_herm_cong
-- name    : PI.UnimodularOrthogonalQuadratic.Loc.herm_cong
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:30:47.521474+00:00
-- url     : https://prove2.me/theorems/4e2443cc-2b1f-41ba-ba3b-b1fe7715901d
-- title:
--   Loc: herm cong
-- statement:
--   The Loc construction uses the herm cong property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularOrthogonal/LocalOrthogonalMatrixOddPrime.lean#L43-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularOrthogonal/LocalOrthogonalMatrixOddPrime.lean#L43-L45

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

theorem PI.UnimodularOrthogonalQuadratic.Loc.herm_cong {n : ℕ} (P : Matrix (Fin n) (Fin n) S) {H : Matrix (Fin n) (Fin n) S} (hH : Hᴴ = H) :
    (P * H * Pᴴ)ᴴ = P * H * Pᴴ := by sorry
