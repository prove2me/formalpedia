-- Prove2me | Theorems.Thm_PositivityTheory_ThKG_Fub_Sys_prod
-- name    : PositivityTheory.ThKG.Fub.Sys.prod
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T09:03:58.911544+00:00
-- url     : https://prove2.me/theorems/8dba4824-3438-4173-8b0b-3871d95a5603
-- title:
--   Sys: prod
-- statement:
--   The Sys construction uses the prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ConeShifts/FubGen.lean#L131-L189
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ConeShifts/FubGen.lean#L131-L189

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ConeShifts_FubGen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKG PositivityTheory.ThKG.Fub
open MeasureTheory Topology Filter
open scoped NNReal
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G]
variable {S A B : Subgroup G} {p q : G →* G}
variable {R : Type} [CommRing R]
variable {P : R → G →* G} {K : Subgroup G} {U : Set G} {good : R → Prop}

theorem PositivityTheory.ThKG.Fub.Sys.prod (s : Sys P K U good) {ι : Type} [DecidableEq ι] (e : ι → R) (he : ∀ i, good (e i))
    (ho : ∀ i j, i ≠ j → e i * e j = 0) (c : R) (hc : good c) (α : ∀ i, Measure (part P K (e i)))
    (hα : ∀ i, (α i).IsHaarMeasure ∧ α i {x | x.1 ∈ U} = 1) (β : Measure (part P K c))
    (hβ : β.IsHaarMeasure ∧ β {x | x.1 ∈ U} = 1) (T : Finset ι) (hT : ∀ i ∈ T, e i * c = 0)
    (hCO : ∀ T' ⊆ T, CO P K U (∑ i ∈ T', e i + c)) (b : R) (hb : b = ∑ i ∈ T, e i + c)
    (μ : Measure (part P K b)) (hμ : μ.IsHaarMeasure ∧ μ {x | x.1 ∈ U} = 1) (f : ι → G → ℂ) (g : G → ℂ)
    (hf : ∀ i ∈ T, Integrable (fun x : part P K (e i) => f i x) (α i)) (hg : Integrable (fun x : part P K c => g x) β) :
    Integrable (fun x : part P K b => (∏ i ∈ T, f i (P (e i) x)) * g (P c x)) μ ∧
      ∫ x : part P K b, (∏ i ∈ T, f i (P (e i) x)) * g (P c x) ∂μ =
        (∏ i ∈ T, ∫ x : part P K (e i), f i x ∂(α i)) * ∫ x : part P K c, g x ∂β := by sorry
