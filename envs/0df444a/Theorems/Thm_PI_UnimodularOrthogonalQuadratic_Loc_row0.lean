-- Prove2me | Theorems.Thm_PI_UnimodularOrthogonalQuadratic_Loc_row0
-- name    : PI.UnimodularOrthogonalQuadratic.Loc.row0
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:30:12.957791+00:00
-- url     : https://prove2.me/theorems/e1164b8d-0a22-5d6b-97db-68f6a0252e6c
-- title:
--   Loc: row0
-- statement:
--   The Loc construction uses the row0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularOrthogonal/LocalOrthogonalMatrixOddPrime.lean#L92-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularOrthogonal/LocalOrthogonalMatrixOddPrime.lean#L92-L99

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

theorem PI.UnimodularOrthogonalQuadratic.Loc.row0 {n : ℕ} {A : Matrix (Fin (n + 1)) (Fin (n + 1)) S} (hA : Aᴴ = A) (h : A 0 0 = 1) (b : Fin (n + 1)) :
    (elim A * A * (elim A)ᴴ) 0 b = if b = 0 then 1 else 0 := by sorry
