-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_PLAux_slice_mInt
-- name    : ReciprocityTheory.AnForm.M.PLAux.slice_mInt
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T13:02:15.635834+00:00
-- url     : https://prove2.me/theorems/794c845d-d3a6-56bf-836a-f4bfd4a458ce
-- title:
--   PLAux: slice m Int
-- statement:
--   The PLAux construction uses the slice m Int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/ContDiffMulOfTsupport.lean#L13-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/ContDiffMulOfTsupport.lean#L13-L57

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffHypInclAt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffMulOfTsupport
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.M.PLAux
open MeasureTheory FinHolAtlas Filter Topology
open ReciprocityTheory.AnForm.A (hypInclAt densHypAt)
open scoped ContDiff Manifold
noncomputable section
variable {e : ℕ} {X : Type} [TopologicalSpace X] [T2Space X] [CompactSpace X]

theorem ReciprocityTheory.AnForm.M.PLAux.slice_mInt {A : FinHolAtlas (e + 1) X} {W : Set X} [CompactSpace W]
    {ψ : OpenPartialHomeomorph X (Fin (e + 1) → ℂ)} {i : Fin (e + 1)}
    (B : FinHolAtlas e W) (hB : HoloMap B A Subtype.val) (Φ : Fin e → LocPot X)
    (hΦ : ∀ k, IsPotential A (Φ k)) (hψ : IsCompatChart A ψ)
    (hWψ : W ∩ ψ.source = {p ∈ ψ.source | ψ p i = 0}) (x : X) {V : Set X}
    (hV : IsOpen V) (hVψ : V ⊆ ψ.source) (hVΦ : ∀ k, V ⊆ (Φ k).U x)
    (hxW : x ∉ W → V ∩ W = ∅) {v : X → ℝ} (hv : A.Smooth v) (hvV : tsupport v ⊆ V) :
    mInt B (fun k => (Φ k).pullback Subtype.val continuous_subtype_val) (v ∘ Subtype.val) =
      ∫ z, chartExt ψ v (hypInclAt i z) * densHypAt i (fun k => (Φ k).φ x ∘ ψ.symm) z := by sorry
