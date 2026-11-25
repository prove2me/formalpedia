-- Prove2me | Theorems.Thm_PI_UnimodularOrthogonalQuadratic_Loc_elim_mul_col
-- name    : PI.UnimodularOrthogonalQuadratic.Loc.elim_mul_col
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:30:29.790627+00:00
-- url     : https://prove2.me/theorems/2ad638b8-d1ee-471c-af3f-1c0c6c6b30ea
-- title:
--   Loc: elim mul col
-- statement:
--   The Loc construction uses the elim mul col property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularOrthogonal/LocalOrthogonalMatrixOddPrime.lean#L86-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularOrthogonal/LocalOrthogonalMatrixOddPrime.lean#L86-L90

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

theorem PI.UnimodularOrthogonalQuadratic.Loc.elim_mul_col {n : ℕ} {A : Matrix (Fin (n + 1)) (Fin (n + 1)) S} (h : A 0 0 = 1) (a : Fin (n + 1)) :
    (elim A * A) a 0 = if a = 0 then 1 else 0 := by sorry
