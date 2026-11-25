-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_QmBorderES_rowPart
-- name    : PI.UnitaryGroupMassFormula.QmBorderES.rowPart
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:39:37.584964+00:00
-- url     : https://prove2.me/theorems/940f6a46-fe80-49ac-ba8d-46f4953bec03
-- title:
--   Qm Border ES: row Part
-- statement:
--   The Qm Border ES construction uses the row Part property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BorderSignIdentity/SkipOneEqSuccAbove.lean#L60-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BorderSignIdentity/SkipOneEqSuccAbove.lean#L60-L69

import Definitions.Def_Formalism_PeriodIntegrals_QmBorderES
import Definitions.Def_Formalism_PeriodIntegrals_QmColExp
import Definitions.Def_Formalism_PeriodIntegrals_QmRowExp
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BorderSignIdentity_SkipOneEqSuccAbove
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
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.QmBorderES

theorem PI.UnitaryGroupMassFormula.QmBorderES.rowPart (hR : PI.ExpLastRow) {A : Type} [Ring A] [Algebra ℂ A] {n t : ℕ} (E : Fin n → Fin n → A)
    (hG : GlRel E) (e : Fin n) (f : Fin t → Fin n) (b : Fin (t + 1) → Fin n) (he : ∀ x, b x ≠ e) (u : ℂ) :
    qminor E (PI.bE e f) b u = ∑ x : Fin (t + 1), (((-1 : ℤ) ^ (x : ℕ) : ℤ) : A) *
      (qminor E f (b ∘ x.succAbove) (u - 1) * E e (b x)) := by sorry
