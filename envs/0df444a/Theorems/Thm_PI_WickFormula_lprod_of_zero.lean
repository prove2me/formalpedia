-- Prove2me | Theorems.Thm_PI_WickFormula_lprod_of_zero
-- name    : PI.WickFormula.lprod_of_zero
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:47:22.948803+00:00
-- url     : https://prove2.me/theorems/8264d533-5f42-48a8-aa8a-c0e1edf83f20
-- title:
--   Wick Formula: lprod of zero
-- statement:
--   The Wick Formula construction uses the lprod of zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/DiscriminantEstimates/DiscriminantLemmas/WickFormula/LprodAddSmul.lean#L10-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/DiscriminantEstimates/DiscriminantLemmas/WickFormula/LprodAddSmul.lean#L10-L12

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_WickFormula_OrdEvalEqSumOf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_WickFormula_LprodAddSmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open PI PI.WickFormula
variable {AA : Type} [Ring AA]

theorem PI.WickFormula.lprod_of_zero {n : ℕ} (c : Fin n → AA) (e : Fin n → ℕ) (h : ∀ i, e i = 0) : lprod c e = 1 := by sorry
