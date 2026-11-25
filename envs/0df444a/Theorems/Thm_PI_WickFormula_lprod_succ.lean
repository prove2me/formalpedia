-- Prove2me | Theorems.Thm_PI_WickFormula_lprod_succ
-- name    : PI.WickFormula.lprod_succ
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:46:50.001803+00:00
-- url     : https://prove2.me/theorems/abce6a7c-5159-4b69-8b8e-a6d0a9bc6621
-- title:
--   Wick Formula: lprod succ
-- statement:
--   The Wick Formula construction uses the lprod succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/DiscriminantEstimates/DiscriminantLemmas/WickFormula/OrdEvalEqSumOf.lean#L12-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/DiscriminantEstimates/DiscriminantLemmas/WickFormula/OrdEvalEqSumOf.lean#L12-L14

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_WickFormula_DeltaEqGdelta
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_WickFormula_OrdEvalEqSumOf
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

theorem PI.WickFormula.lprod_succ {n : ℕ} (c : Fin (n + 1) → AA) (e : Fin (n + 1) → ℕ) :
    lprod c e = c 0 ^ e 0 * lprod (fun i => c i.succ) (fun i => e i.succ) := by sorry
