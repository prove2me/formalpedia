-- Prove2me | Theorems.Thm_PositivityTheory_ThKCT_Unf_eq_smul
-- name    : PositivityTheory.ThKCT.Unf.eq_smul
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:50:19.27654+00:00
-- url     : https://prove2.me/theorems/2d1fbc3e-818e-5469-ab36-2be012273163
-- title:
--   Unf: eq smul
-- statement:
--   The Unf construction uses the eq smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/SmallCones/RightOfCompact.lean#L114-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/SmallCones/RightOfCompact.lean#L114-L137

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_SmallCones_RightOfCompact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Set
open scoped ENNReal NNReal Pointwise
open PositivityTheory PositivityTheory.ThKCT PositivityTheory.ThKCT.Unf
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
variable (ν : Measure G) [ν.IsHaarMeasure] (m : Measure G) [SFinite m] {P : Set G} {K : Subgroup G}

theorem PositivityTheory.ThKCT.Unf.eq_smul [IsFiniteMeasureOnCompacts m] (hP : ∀ p ∈ P, m.map (p * ·) = m) (hK : ∀ k ∈ K, m.map (· * k) = m)
    (hKc : IsCompact (K : Set G)) (hPK : ∀ g, ∃ p ∈ P, ∃ k ∈ K, g = p * k) : ∃ c : ℝ≥0∞, c ≠ ⊤ ∧ m = c • ν := by sorry
