-- Prove2me | Theorems.Thm_PI_UnimodularOrthogonalQuadratic_Loc_q_smul
-- name    : PI.UnimodularOrthogonalQuadratic.Loc.q_smul
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:30:35.418079+00:00
-- url     : https://prove2.me/theorems/a9db7718-653f-4c5e-8b49-aaf55f95beaa
-- title:
--   Loc: q smul
-- statement:
--   The Loc construction uses the q smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularOrthogonal/LocalOrthogonalMatrixOddPrime.lean#L22-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularOrthogonal/LocalOrthogonalMatrixOddPrime.lean#L22-L26

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

theorem PI.UnimodularOrthogonalQuadratic.Loc.q_smul {n : ℕ} (H : Matrix (Fin n) (Fin n) S) (u : S) (v : Fin n → S) :
    q H (u • v) = u * star u * q H v := by sorry
