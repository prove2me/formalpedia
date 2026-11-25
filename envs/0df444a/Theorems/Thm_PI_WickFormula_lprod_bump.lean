-- Prove2me | Theorems.Thm_PI_WickFormula_lprod_bump
-- name    : PI.WickFormula.lprod_bump
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:47:03.209966+00:00
-- url     : https://prove2.me/theorems/3106c87f-5cf9-4c7e-b182-1e0a472887f5
-- title:
--   Wick Formula: lprod bump
-- statement:
--   The Wick Formula construction uses the lprod bump property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/DiscriminantEstimates/DiscriminantLemmas/WickFormula/OrdEvalEqSumOf.lean#L16-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/DiscriminantEstimates/DiscriminantLemmas/WickFormula/OrdEvalEqSumOf.lean#L16-L31

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

theorem PI.WickFormula.lprod_bump {n : ℕ} (c : Fin n → AA) (hc : ∀ i i', Commute (c i) (c i'))
    (e e' : Fin n → ℕ) (i : Fin n) (h1 : e' i = e i + 1) (h2 : ∀ i', i' ≠ i → e' i' = e i') :
    lprod c e' = c i * lprod c e := by sorry
