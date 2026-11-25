-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_QmBorderFull_Four_inner
-- name    : PI.UnitaryGroupMassFormula.QmBorderFull.Four.inner
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:44:42.998249+00:00
-- url     : https://prove2.me/theorems/ab221bcf-a889-4ecf-8443-f7b9399b1ab9
-- title:
--   Four: inner
-- statement:
--   The Four construction uses the inner property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BorderMinorRotation/SkipTwoSuccAboveComp.lean#L90-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BorderMinorRotation/SkipTwoSuccAboveComp.lean#L90-L100

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BorderMinorRotation_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BorderMinorRotation_SkipTwoSuccAboveComp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Formalism.REAL
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.QmBorderFull PI.UnitaryGroupMassFormula.QmBorderFull.Four
open PI

theorem PI.UnitaryGroupMassFormula.QmBorderFull.Four.inner (hR : ExpLastRow) (hF : ExpFirstRow) {A : Type} [Ring A] [Algebra ℂ A] {n t : ℕ}
    (E : Fin n → Fin n → A) (hG : GlRel E) (e es : Fin n) (W : Fin t → Fin n) (b : Fin (t + 2) → Fin n)
    (he : ∀ x, b x ≠ e) (hes : ∀ x, b x ≠ es) (z : ℂ) :
    qminor E (bE e (bS W es)) b z = ∑ x : Fin (t + 2), ∑ y : Fin (t + 1),
      (((-1 : ℤ) ^ ((x : ℕ) + t + (y : ℕ)) : ℤ) : A) *
        (E es (b (x.succAbove y)) * qminor E W ((b ∘ x.succAbove) ∘ y.succAbove) (z - 1) * E e (b x)) := by sorry
