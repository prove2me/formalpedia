-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_QmBorderES_colPart
-- name    : PI.UnitaryGroupMassFormula.QmBorderES.colPart
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:32:51.833619+00:00
-- url     : https://prove2.me/theorems/0c455926-b771-4b91-8e9f-b141ca38c6f8
-- title:
--   Qm Border ES: col Part
-- statement:
--   The Qm Border ES construction uses the col Part property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BorderSignIdentity/SkipOneEqSuccAbove.lean#L71-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BorderSignIdentity/SkipOneEqSuccAbove.lean#L71-L79

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

theorem PI.UnitaryGroupMassFormula.QmBorderES.colPart (hF : PI.ExpFirstRow) {A : Type} [Ring A] [Algebra ℂ A] {n t : ℕ} (E : Fin n → Fin n → A)
    (hG : GlRel E) (e : Fin n) (f : Fin t → Fin n) (b : Fin (t + 1) → Fin n) (he : ∀ x, b x ≠ e) (u : ℂ) :
    qminor E (PI.bS f e) b u = ∑ x : Fin (t + 1), (((-1 : ℤ) ^ (t + (x : ℕ)) : ℤ) : A) *
      (E e (b x) * qminor E f (b ∘ x.succAbove) u) := by sorry
