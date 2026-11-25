-- Prove2me | Theorems.Thm_PositivityTheory_ThKEnd_Two_bump_ex
-- name    : PositivityTheory.ThKEnd.Two.bump_ex
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:50:23.27514+00:00
-- url     : https://prove2.me/theorems/146dfbf0-d455-4fea-8204-32e65477f6ee
-- title:
--   Two: bump ex
-- statement:
--   The Two construction uses the bump ex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/EigenvalueEndgame/SignatureSplitting/ClosedEmb.lean#L112-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/EigenvalueEndgame/SignatureSplitting/ClosedEmb.lean#L112-L156

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

theorem PositivityTheory.ThKEnd.Two.bump_ex [T2Space R] {V Λ : Type} [NormedCommRing V] [CommRing Λ] [TopologicalSpace Λ] [IsTopologicalRing Λ]
    (p : R →+* V) (q : R →+* Λ) (hp : Continuous p) (hq : Continuous q)
    (hc : ∀ (r : ℝ) (C : Set Λ), IsCompact C → IsCompact {x | ‖p x‖ ≤ r ∧ q x ∈ C})
    (hn : ∀ O ∈ 𝓝 (0 : R), ∃ ε > 0, ∃ U ∈ 𝓝 (0 : Λ), ∀ x, ‖p x‖ ≤ ε → q x ∈ U → x ∈ O)
    (hL : ∀ U ∈ 𝓝 (0 : Λ), ∃ L : AddSubgroup Λ, IsOpen (L : Set Λ) ∧ IsCompact (L : Set Λ) ∧ (L : Set Λ) ⊆ U)
    {W : Set SL(2, R)} (hW : W ∈ 𝓝 1) : ∃ η, Bump W η ∧ ∃ L : AddSubgroup Λ, IsOpen (L : Set Λ) ∧ ∀ (y y' : SL(2, R)) (b : ℝ),
      (∀ i j, q ((y.1 - y'.1) i j) ∈ L ∧ ‖p ((y.1 - y'.1) i j)‖ ≤ b) → |η y' - η y| ≤ 4 * b := by sorry
