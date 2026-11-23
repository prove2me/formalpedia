-- Prove2me | Theorems.Thm_PI_UnimodularOrthogonalQuadratic_Loc_det_of_first_row_single
-- name    : PI.UnimodularOrthogonalQuadratic.Loc.det_of_first_row_single
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:42:55.314791+00:00
-- url     : https://prove2.me/theorems/2cfa74b6-3ff4-4210-877f-5a7a12aed3e0
-- title:
--   Loc: det of first row single
-- statement:
--   The Loc construction uses the det of first row single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularOrthogonal/LocalOrthogonalMatrixOddPrime.lean#L101-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularOrthogonal/LocalOrthogonalMatrixOddPrime.lean#L101-L104

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

theorem PI.UnimodularOrthogonalQuadratic.Loc.det_of_first_row_single {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) S) (h : ∀ b, M 0 b = if b = 0 then 1 else 0) :
    M.det = (M.submatrix Fin.succ Fin.succ).det := by sorry
