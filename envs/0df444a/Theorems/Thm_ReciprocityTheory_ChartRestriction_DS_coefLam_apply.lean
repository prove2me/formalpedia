-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_coefLam_apply
-- name    : ReciprocityTheory.ChartRestriction.DS.coefLam_apply
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T09:50:10.957932+00:00
-- url     : https://prove2.me/theorems/695af79c-c485-4ee2-b637-b49d4b6c37e4
-- title:
--   DS: coef Lam apply
-- statement:
--   The DS construction uses the coef Lam apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/CoefETensGrpMul.lean#L39-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/CoefETensGrpMul.lean#L39-L41

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CoefDTensActPow
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CoefETensGrpMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open scoped Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ D}

theorem ReciprocityTheory.ChartRestriction.DS.coefLam_apply (dual : Bool) (g : Matrix (Fin n) (Fin n) ℂ) (f u : Fin n → H) :
    coefLam dual σ g f u = ∑ c, inner ℂ (f c) (coefTG dual σ g u c) := by sorry
