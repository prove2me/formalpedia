-- Prove2me | Theorems.Thm_PI_MSC_reorder
-- name    : PI.MSC.reorder
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:35:28.371024+00:00
-- url     : https://prove2.me/theorems/a59aeeb1-1098-4092-a968-5a217448effc
-- title:
--   MSC: reorder
-- statement:
--   The MSC construction uses the reorder property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MinorSpanComplement/ShapeColumnDegreeColumnSizes.lean#L86-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MinorSpanComplement/ShapeColumnDegreeColumnSizes.lean#L86-L142

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinorSpanComplement_ShapeColumnDegreeColumnSizes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
open PI PI.MSC

theorem PI.MSC.reorder (R : Type) [CommRing R] (ν : YoungDiagram) (N : ℕ) {K : ℕ} (sz : Fin K → ℕ)
    (hsz : ∀ k, sz k ≤ ν.colLen 0) (I : ∀ k, Fin (sz k) → Fin N) (hI : ∀ k, StrictMono (I k))
    (hsh : shapeDeg sz = nuR ν) :
    ∃ J : ∀ c : Fin (ν.rowLen 0), Fin (sz0 ν c) → Fin N, (∀ c, StrictMono (J c)) ∧
      bideterminant R sz hsz I = bideterminant R (sz0 ν) (hsz0 ν) J := by sorry
