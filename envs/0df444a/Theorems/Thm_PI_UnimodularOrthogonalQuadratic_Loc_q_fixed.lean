-- Prove2me | Theorems.Thm_PI_UnimodularOrthogonalQuadratic_Loc_q_fixed
-- name    : PI.UnimodularOrthogonalQuadratic.Loc.q_fixed
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:30:14.753945+00:00
-- url     : https://prove2.me/theorems/ff914716-7518-508b-b15a-fbf990dbc8fe
-- title:
--   Loc: q fixed
-- statement:
--   The Loc construction uses the q fixed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularOrthogonal/LocalOrthogonalMatrixOddPrime.lean#L32-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularOrthogonal/LocalOrthogonalMatrixOddPrime.lean#L32-L37

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

theorem PI.UnimodularOrthogonalQuadratic.Loc.q_fixed {n : ℕ} {H : Matrix (Fin n) (Fin n) S} (hH : Hᴴ = H) (v : Fin n → S) :
    star (q H v) = q H v := by sorry
