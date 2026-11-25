-- Prove2me | Theorems.Thm_PI_WickFormula_lprod_add_smul
-- name    : PI.WickFormula.lprod_add_smul
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:46:50.821635+00:00
-- url     : https://prove2.me/theorems/53b6f478-237b-4f5e-8e93-dc540de8f53e
-- title:
--   Wick Formula: lprod add smul
-- statement:
--   The Wick Formula construction uses the lprod add smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/DiscriminantEstimates/DiscriminantLemmas/WickFormula/LprodAddSmul.lean#L22-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/DiscriminantEstimates/DiscriminantLemmas/WickFormula/LprodAddSmul.lean#L22-L42

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

theorem PI.WickFormula.lprod_add_smul {M : Type} [AddCommGroup M] [Module AA M] {n : ℕ} (x y : Fin n → AA)
    (e : Fin n → ℕ) (v : M) (hxy : ∀ i j, Commute (y i) (x j)) (hy : ∀ i, y i • v = 0) :
    lprod (x + y) e • v = lprod x e • v := by sorry
