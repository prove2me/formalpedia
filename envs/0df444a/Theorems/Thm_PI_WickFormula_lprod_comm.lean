-- Prove2me | Theorems.Thm_PI_WickFormula_lprod_comm
-- name    : PI.WickFormula.lprod_comm
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:46:53.177047+00:00
-- url     : https://prove2.me/theorems/e2d9e564-e95a-4eb5-ac9e-d8f251ff4474
-- title:
--   Wick Formula: lprod comm
-- statement:
--   The Wick Formula construction uses the lprod comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/DiscriminantEstimates/DiscriminantLemmas/WickFormula/LprodAddSmul.lean#L76-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/DiscriminantEstimates/DiscriminantLemmas/WickFormula/LprodAddSmul.lean#L76-L90

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
variable {k AA : Type} [CommRing k] [Ring AA] [Algebra k AA]

theorem PI.WickFormula.lprod_comm {n : ℕ} (c : Fin n → AA) (hc : ∀ i i', Commute (c i) (c i')) (b : AA) (t : Fin n → k)
    (h : ∀ j, b * c j = c j * b + algebraMap k AA (t j)) (e : Fin n → ℕ) :
    b * lprod c e = lprod c e * b +
      ∑ j, ((e j : k) * t j) • lprod c (fun j' => e j' - if j = j' then 1 else 0) := by sorry
