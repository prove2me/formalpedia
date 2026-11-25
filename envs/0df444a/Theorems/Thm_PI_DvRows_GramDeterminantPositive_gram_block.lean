-- Prove2me | Theorems.Thm_PI_DvRows_GramDeterminantPositive_gram_block
-- name    : PI.DvRows.GramDeterminantPositive.gram_block
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:29:29.072102+00:00
-- url     : https://prove2.me/theorems/136d2989-cd37-4888-9826-2b7912be7f61
-- title:
--   Gram Determinant Positive: gram block
-- statement:
--   The Gram Determinant Positive construction uses the gram block property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionRows/MulVecInjectiveOfKer.lean#L129-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionRows/MulVecInjectiveOfKer.lean#L129-L167

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_Pieces
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_MulVecInjectiveOfKer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.DvRows
open PI.DvRows.GramDeterminantPositive
open Matrix
open scoped ComplexOrder
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {m : Type*} [Fintype m] [DecidableEq m]

theorem PI.DvRows.GramDeterminantPositive.gram_block {k d : Type*} [Fintype k] [DecidableEq k] [Fintype d] [DecidableEq d]
    (Uc : Matrix m k ℂ) (Zc Ac : Matrix m d ℂ) (T : Matrix (k ⊕ d) d ℂ)
    (hT : Ac = fromCols Uc Zc * T) (hAU : Acᴴ * Uc = 0) (hg : (Ucᴴ * Uc).det ≠ 0) :
    (Ucᴴ * Uc).det * ((Acᴴ * Zc).det * star (Acᴴ * Zc).det) =
      (Acᴴ * Ac).det * ((fromCols Uc Zc)ᴴ * fromCols Uc Zc).det := by sorry
