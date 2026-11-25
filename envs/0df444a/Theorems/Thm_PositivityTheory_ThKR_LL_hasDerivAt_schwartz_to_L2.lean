-- Prove2me | Theorems.Thm_PositivityTheory_ThKR_LL_hasDerivAt_schwartz_to_L2
-- name    : PositivityTheory.ThKR.LL.hasDerivAt_schwartz_to_L2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:05:15.942837+00:00
-- url     : https://prove2.me/theorems/044cd527-5914-44ff-b939-a934171c94cd
-- title:
--   LL: has Deriv At schwartz to L2
-- statement:
--   The LL construction uses the has Deriv At schwartz to L2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/HasDerivAtSchwartzToL2.lean#L22-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/HasDerivAtSchwartzToL2.lean#L22-L68

import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_MetaDef
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_HasDerivAtSchwartzToL2
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil PositivityTheory.ThKF.E Filter Topology
open scoped Real
open PositivityTheory PositivityTheory.ThKR PositivityTheory.ThKR.LL
variable {l : Type} [Fintype l]

theorem PositivityTheory.ThKR.LL.hasDerivAt_schwartz_to_L2 {F : ℝ → Sch l} {G : Sch l} {t₀ : ℝ} (hp : ∀ x, HasDerivAt (fun t => F t x) (G x) t₀) {C : ℝ}
    (hb : ∀ᶠ t in 𝓝 t₀, ∀ x, (1 + ‖x‖) ^ (Module.finrank ℝ (EuclideanSpace ℝ l) + 1) * ‖F t x - F t₀ x‖ ≤ C * |t - t₀|) :
    HasDerivAt (fun t => schwartzToL2 l (F t)) (schwartzToL2 l G) t₀ := by sorry
