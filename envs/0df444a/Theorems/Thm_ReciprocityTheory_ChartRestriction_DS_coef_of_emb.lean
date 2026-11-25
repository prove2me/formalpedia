-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_coef_of_emb
-- name    : ReciprocityTheory.ChartRestriction.DS.coef_of_emb
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T14:25:11.80827+00:00
-- url     : https://prove2.me/theorems/cb8d0225-6826-411c-82e9-c9476c03e659
-- title:
--   DS: coef of emb
-- statement:
--   The DS construction uses the coef of emb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/CoefOfEmb.lean#L17-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/CoefOfEmb.lean#L17-L54

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_HidaSetting
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CoefBTensSubKStable
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CoefETensGrpMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CoefOfEmb
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}

theorem ReciprocityTheory.ChartRestriction.DS.coef_of_emb (dual : Bool) {lam lam' : Fin n → ℝ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {ε : Fin n → Bool}
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}
    (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {V : Submodule ℂ D} (hgap : StdGap ε lam) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) {V' : Submodule ℂ D} (hgap' : StdGap ε lam') (hV' : IsKIrrHW ε E (lowK ε lam') V')
    (hc' : ∀ v ∈ V', casimir E v = (casVal lam' : ℂ) • v)
    (hVK' : ∀ k ∈ Kset ε, ∀ v ∈ V', ∃ w ∈ V', (w : H) = σ k v)
    {ι : D →ₗ[ℂ] (Fin n → D)} (hι : IsGKEmb dual ε σ E (genSub E V) (genSub E V') ι) :
    (∀ f ∈ tensSub (genSub E V), ∀ x' ∈ genSub E V', ∃ z ∈ genSub E V', ∀ g ∈ UJset ε,
      ∑ c, inner ℂ ((f c : D) : H) (tensGrp dual σ g (fun d => ((ι x' d : D) : H)) c) =
        inner ℂ ((z : D) : H) (σ g ((x' : D) : H))) ∧
    ∀ z ∈ genSub E V', ∀ x' ∈ genSub E V', ∃ f ∈ tensSub (genSub E V), ∀ g ∈ UJset ε,
      inner ℂ ((z : D) : H) (σ g ((x' : D) : H)) =
        ∑ c, inner ℂ ((f c : D) : H) (tensGrp dual σ g (fun d => ((ι x' d : D) : H)) c) := by sorry
