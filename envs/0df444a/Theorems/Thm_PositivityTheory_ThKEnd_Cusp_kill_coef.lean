-- Prove2me | Theorems.Thm_PositivityTheory_ThKEnd_Cusp_kill_coef
-- name    : PositivityTheory.ThKEnd.Cusp.kill_coef
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T14:00:08.479856+00:00
-- url     : https://prove2.me/theorems/9bbe2c96-2142-439c-8b9e-e544f756a886
-- title:
--   Cusp: kill coef
-- statement:
--   The Cusp construction uses the kill coef property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/EigenvalueEndgame/CuspidalAverages/KillCoef.lean#L14-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/EigenvalueEndgame/CuspidalAverages/KillCoef.lean#L14-L60

import Definitions.Def_Development_WeilBound_ThetaLifts_EigenvalueEndgame_SignatureSplitting_ConvCont
import Definitions.Def_Development_WeilBound_ThetaLifts_EigenvalueEndgame_CuspidalAverages_KillCoef
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKEnd PositivityTheory.ThKEnd.Cusp
open MeasureTheory Topology Filter PositivityTheory.ThKEnd.Two
open scoped Pointwise
variable {G X : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] {Γ : Subgroup G} {n : X → G}
  {a : G} {lam : Measure X} [IsProbabilityMeasure lam] {φ c : G → ℂ}

theorem PositivityTheory.ThKEnd.Cusp.kill_coef (hC : Cusp Γ n a) (hn : Continuous n) {e : X → ℂ} (ce : Continuous e) (ne : ∀ x, ‖e x‖ ≤ 1) (b : ℕ → G) {y : ℕ → ℂ}
    (hy : Tendsto (fun i => ‖y i‖) atTop atTop) {m : ℕ} (h : Dat Γ n a lam 0 φ c) (hm : Gr a m φ) {V : Set G} (hV : V ∈ 𝓝 1)
    (H : ∀ z ∈ V, ∀ i, y 0 * ∫ x, e x * φ (n x * (b i * z)) ∂lam = y i * ∫ x, e x * φ (n x * z) ∂lam) :
    ∫ x, e x * φ (n x * 1) ∂lam = 0 := by sorry
