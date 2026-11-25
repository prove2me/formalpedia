-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_coefE_tensGrp_mul
-- name    : ReciprocityTheory.ChartRestriction.DS.coefE_tensGrp_mul
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T09:55:17.596128+00:00
-- url     : https://prove2.me/theorems/6cd3e68b-972a-48a6-910b-8bebeb9f3c11
-- title:
--   DS: coef E tens Grp mul
-- statement:
--   The DS construction uses the coef E tens Grp mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/CoefETensGrpMul.lean#L22-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/CoefETensGrpMul.lean#L22-L28

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

theorem ReciprocityTheory.ChartRestriction.DS.coefE_tensGrp_mul (dual : Bool) (hσ : IsURepOn (UJset ε) σ) {g h : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ UJset ε) (hh : h ∈ UJset ε) (w : Fin n → H) :
    coefTG dual σ (g * h) w = coefTG dual σ g (coefTG dual σ h w) := by sorry
