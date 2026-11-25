-- Prove2me | Theorems.Thm_PIW_AdelClassFin_hmk_box
-- name    : PIW.AdelClassFin.hmk_box
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:47:27.086567+00:00
-- url     : https://prove2.me/theorems/c2ff6d19-aec8-4c15-a931-eeb47befeeef
-- title:
--   Adel Class Fin: hmk box
-- statement:
--   The Adel Class Fin construction uses the hmk box property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/HmkFactor.lean#L31-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/HmkFactor.lean#L31-L99

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_HformSelfStar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_HmkFactor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PIW PIW.AdelClassFin
open MeasureTheory Matrix Module
open scoped MatrixOrder

theorem PIW.AdelClassFin.hmk_box {N : ℕ} (hN : 1 ≤ N) (B : Matrix (Fin N) (Fin N) ℝ) (hB : B.det ≠ 0) :
    ∃ c : Fin N → ℤ, c ≠ 0 ∧
      ∀ i, |(B *ᵥ fun j => (c j : ℝ)) i| ≤ 2 * |B.det| ^ ((1 : ℝ) / N) := by sorry
