-- Prove2me | Theorems.Thm_PositivityTheory_ThKEnd_Two_lip_of
-- name    : PositivityTheory.ThKEnd.Two.lip_of
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T14:00:41.014723+00:00
-- url     : https://prove2.me/theorems/52fcb9f3-fda0-5a12-9414-2ad2e24c55ff
-- title:
--   Two: lip of
-- statement:
--   The Two construction uses the lip of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/EigenvalueEndgame/SignatureSplitting/ClosedEmb.lean#L158-L217
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/EigenvalueEndgame/SignatureSplitting/ClosedEmb.lean#L158-L217

import Definitions.Def_Development_WeilBound_ThetaLifts_EigenvalueEndgame_SignatureSplitting_ConvCont
import Definitions.Def_Development_WeilBound_ThetaLifts_EigenvalueEndgame_SignatureSplitting_ClosedEmb
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
set_option linter.unusedSectionVars false
open PositivityTheory PositivityTheory.ThKEnd PositivityTheory.ThKEnd.Two
open MeasureTheory Topology Filter Matrix NumberField IsDedekindDomain
open scoped Pointwise MatrixGroups
variable {R : Type} [CommRing R]
variable [TopologicalSpace R] [IsTopologicalRing R]

theorem PositivityTheory.ThKEnd.Two.lip_of [T2Space R] {V Λ : Type} [NormedCommRing V] [CommRing Λ] [TopologicalSpace Λ] [IsTopologicalRing Λ]
    (p : R →+* V) (q : R →+* Λ) (hp : Continuous p) (hq : Continuous q)
    (hc : ∀ (r : ℝ) (C : Set Λ), IsCompact C → IsCompact {x | ‖p x‖ ≤ r ∧ q x ∈ C})
    (hn : ∀ O ∈ 𝓝 (0 : R), ∃ ε > 0, ∃ U ∈ 𝓝 (0 : Λ), ∀ x, ‖p x‖ ≤ ε → q x ∈ U → x ∈ O) {Γ : Subgroup SL(2, R)}
    (hL : ∀ U ∈ 𝓝 (0 : Λ), ∃ L : AddSubgroup Λ, IsOpen (L : Set Λ) ∧ IsCompact (L : Set Λ) ∧ (L : Set Λ) ⊆ U ∧
      ∃ D : ℝ, ∀ x : R, ∃ ξ, uni (.ofAdd ξ) ∈ Γ ∧ ‖p (ξ + x)‖ ≤ D ∧ q (ξ + x) ∈ L)
    {u : Rˣ} (hu : ‖p (u⁻¹).1‖ ≤ 1 / 2) (hu' : q (u⁻¹).1 = 1) (W : Set SL(2, R)) (hW : W ∈ 𝓝 1) :
    ∃ η, Bump W η ∧ ∀ Ω : Set SL(2, R), IsCompact Ω → ∃ (D : ℝ) (Ω' : Set SL(2, R)), IsCompact Ω' ∧ ∀ x (k : ℕ),
      ∃ γ ∈ Γ, ∃ v ∈ Ω', γ * uni x * dia u ^ k = dia u ^ k * v ∧
        ∀ κ ∈ Ω, ∀ y, |η (κ⁻¹ * (v⁻¹ * y)) - η (κ⁻¹ * y)| ≤ D / 2 ^ k := by sorry
