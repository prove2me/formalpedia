-- Prove2me | Theorems.Thm_PI_QmRowExpWork_qminorRow_succ
-- name    : PI.QmRowExpWork.qminorRow_succ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:38:49.715776+00:00
-- url     : https://prove2.me/theorems/f1f50913-033c-497f-9382-5cb7c0c8fa2a
-- title:
--   Qm Row Exp Work: qminor Row succ
-- statement:
--   The Qm Row Exp Work construction uses the qminor Row succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RowExpansionMinor/FirstColumnSplitBijective.lean#L61-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RowExpansionMinor/FirstColumnSplitBijective.lean#L61-L69

import Definitions.Def_Formalism_PeriodIntegrals_QmRowExp
import Definitions.Def_Formalism_PeriodIntegrals_QmRowForm
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RowExpansionMinor_FirstColumnSplitBijective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open PI PI.QmRowExpWork
open Formalism.REAL

theorem PI.QmRowExpWork.qminorRow_succ {A : Type*} [Ring A] [Algebra ℂ A] {n m : ℕ} (E : Fin n → Fin n → A)
    (a b : Fin (m + 1) → Fin n) (u : ℂ) :
    qminorRow E a b u = ∑ σ : Equiv.Perm (Fin (m + 1)), ((Equiv.Perm.sign σ : ℤ) : A) *
      (List.ofFn fun k : Fin (m + 1) => Tm E (u - (m : ℂ) + ((k : ℕ) : ℂ)) (a k) (b (σ k))).prod := by sorry
