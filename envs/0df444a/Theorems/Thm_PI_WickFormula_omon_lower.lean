-- Prove2me | Theorems.Thm_PI_WickFormula_omon_lower
-- name    : PI.WickFormula.omon_lower
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:46:56.289597+00:00
-- url     : https://prove2.me/theorems/89f33dca-5243-4bf6-ba49-7095ddcaf4e2
-- title:
--   Wick Formula: omon lower
-- statement:
--   The Wick Formula construction uses the omon lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/DiscriminantEstimates/DiscriminantLemmas/WickFormula/LprodAddSmul.lean#L109-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/DiscriminantEstimates/DiscriminantLemmas/WickFormula/LprodAddSmul.lean#L109-L120

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

theorem PI.WickFormula.omon_lower {AA : Type} [Ring AA] {r s : ℕ} (a : Fin r → AA) (a' : Fin s → AA)
    (m : Fin r ⊕ Fin s →₀ ℕ) (j : Fin s) :
    omon a a' (m - Finsupp.single (Sum.inr j) 1) =
      lprod a (fun i => m (Sum.inl i)) * lprod a' (fun j' => m (Sum.inr j') - if j = j' then 1 else 0) := by sorry
