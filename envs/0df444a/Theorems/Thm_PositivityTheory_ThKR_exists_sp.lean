-- Prove2me | Theorems.Thm_PositivityTheory_ThKR_exists_sp
-- name    : PositivityTheory.ThKR.exists_sp
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:06:01.718465+00:00
-- url     : https://prove2.me/theorems/3d95f3f6-f786-5213-979e-8964e9f7a3c2
-- title:
--   Th KR: exists sp
-- statement:
--   The Th KR construction uses the exists sp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/ExistsSmoothFun.lean#L12-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/ExistsSmoothFun.lean#L12-L138

import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_MetaDef
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_ExistsSmoothFun
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil PositivityTheory.ThKF.E
open scoped Real RealInnerProductSpace FourierTransform
open PositivityTheory PositivityTheory.ThKR
variable {l : Type} [Fintype l] [DecidableEq l]

theorem PositivityTheory.ThKR.exists_sp (s : ℝ → (l ⊕ l → ℝ) →ₗ[ℝ] (l ⊕ l → ℝ))
    (sc : ∀ w, Continuous fun t => s t w) (s0 : ∀ w, s 0 w = w) (sm : ∀ t u w, s (t + u) w = s t (s u w))
    (ss : ∀ t w w', sympl (s t w) (s t w') = sympl w w') :
    ∃ X ∈ LieAlgebra.Symplectic.sp l ℝ, ∀ (t : ℝ) w, s t w = NormedSpace.exp (t • X) *ᵥ w := by sorry
