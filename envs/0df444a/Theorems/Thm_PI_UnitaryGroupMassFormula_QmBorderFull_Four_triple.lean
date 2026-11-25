-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_QmBorderFull_Four_triple
-- name    : PI.UnitaryGroupMassFormula.QmBorderFull.Four.triple
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:40:08.326455+00:00
-- url     : https://prove2.me/theorems/903713f8-59a7-4cd1-8929-ce3f812c455b
-- title:
--   Four: triple
-- statement:
--   The Four construction uses the triple property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BorderMinorRotation/SkipTwoSuccAboveComp.lean#L144-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BorderMinorRotation/SkipTwoSuccAboveComp.lean#L144-L167

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

theorem PI.UnitaryGroupMassFormula.QmBorderFull.Four.triple {M : Type*} [AddCommMonoid M] {k : ℕ} (w : Fin (k + 1))
    (H : Fin (k + 1) → Fin (k + 1) → Fin (k + 1) → M) :
    ∑ w' : Fin (k + 1), ∑ x : Fin (k + 1), ∑ x' : Fin (k + 1), (if w ≠ w' ∧ x ≠ x' then H w' x x' else 0)
      = ∑ j : Fin k, ∑ x' : Fin (k + 1), ∑ y : Fin k, H (w.succAbove j) (x'.succAbove y) x' := by sorry
