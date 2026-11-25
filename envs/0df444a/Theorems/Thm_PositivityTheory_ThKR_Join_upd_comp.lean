-- Prove2me | Theorems.Thm_PositivityTheory_ThKR_Join_upd_comp
-- name    : PositivityTheory.ThKR.Join.upd_comp
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:25:08.108516+00:00
-- url     : https://prove2.me/theorems/87da6a5b-b772-42d3-aa73-6aa200fa68f3
-- title:
--   Join: upd comp
-- statement:
--   The Join construction uses the upd comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/TensJoin.lean#L14-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/TensJoin.lean#L14-L21

import Definitions.Def_Development_WeilBound_ThetaLifts_CartanFactorisation_TensMax
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_TensJoin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
open PiTensorProduct
open PositivityTheory PositivityTheory.ThKR PositivityTheory.ThKR.Join
open PositivityTheory.ThKF.Unit
variable {ι : Type} [Fintype ι] [DecidableEq ι] {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]

theorem PositivityTheory.ThKR.Join.upd_comp (u : ∀ j, V j →ₗ[ℂ] V j) (i : ι) (a : V i →ₗ[ℂ] V i) :
    map (Function.update (fun j => (LinearMap.id : V j →ₗ[ℂ] V j)) i a) ∘ₗ map u = map (Function.update u i (a ∘ₗ u i)) := by sorry
