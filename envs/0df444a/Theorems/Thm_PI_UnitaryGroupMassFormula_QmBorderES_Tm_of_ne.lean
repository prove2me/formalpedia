-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_QmBorderES_Tm_of_ne
-- name    : PI.UnitaryGroupMassFormula.QmBorderES.Tm_of_ne
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:00:51.912319+00:00
-- url     : https://prove2.me/theorems/6041adce-996e-4b48-bcfb-667850f80b8a
-- title:
--   Qm Border ES: Tm of ne
-- statement:
--   The Qm Border ES construction uses the Tm of ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BorderSignIdentity/SkipOneEqSuccAbove.lean#L54-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BorderSignIdentity/SkipOneEqSuccAbove.lean#L54-L56

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

theorem PI.UnitaryGroupMassFormula.QmBorderES.Tm_of_ne {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (u : ℂ) {a b : Fin n}
    (h : a ≠ b) : Tm E u a b = E a b := by sorry
