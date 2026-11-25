-- Prove2me | Theorems.Thm_PI_UnimodularOrthogonalQuadratic_Loc_blk_cong
-- name    : PI.UnimodularOrthogonalQuadratic.Loc.blk_cong
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:31:16.136423+00:00
-- url     : https://prove2.me/theorems/f426ff21-67ab-4660-b0f7-adf3aec51304
-- title:
--   Loc: blk cong
-- statement:
--   The Loc construction uses the blk cong property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularOrthogonal/LocalOrthogonalMatrixOddPrime.lean#L114-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularOrthogonal/LocalOrthogonalMatrixOddPrime.lean#L114-L129

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

theorem PI.UnimodularOrthogonalQuadratic.Loc.blk_cong {n : ℕ} {M : Matrix (Fin (n + 1)) (Fin (n + 1)) S} {P : Matrix (Fin n) (Fin n) S}
    (hrow : ∀ b, M 0 b = if b = 0 then 1 else 0) (hcol : ∀ a, M a 0 = if a = 0 then 1 else 0)
    (hP : P * M.submatrix Fin.succ Fin.succ * Pᴴ = 1) : blk P * M * (blk P)ᴴ = 1 := by sorry
