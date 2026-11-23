-- Prove2me | Theorems.Thm_PI_UnimodularOrthogonalQuadratic_Loc_elimination_mul_first_row
-- name    : PI.UnimodularOrthogonalQuadratic.Loc.elimination_mul_first_row
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:42:54.635067+00:00
-- url     : https://prove2.me/theorems/aa30be44-1d76-44b6-b61e-8746e00d176d
-- title:
--   Loc: elimination mul first row
-- statement:
--   The Loc construction uses the elimination mul first row property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularOrthogonal/LocalOrthogonalMatrixOddPrime.lean#L82-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularOrthogonal/LocalOrthogonalMatrixOddPrime.lean#L82-L84

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

theorem PI.UnimodularOrthogonalQuadratic.Loc.elimination_mul_first_row {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) S) (b : Fin (n + 1)) :
    (elim A * A) 0 b = A 0 b := by sorry
