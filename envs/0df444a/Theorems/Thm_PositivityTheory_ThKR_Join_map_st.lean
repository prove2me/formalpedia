-- Prove2me | Theorems.Thm_PositivityTheory_ThKR_Join_map_st
-- name    : PositivityTheory.ThKR.Join.map_st
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:24:43.549552+00:00
-- url     : https://prove2.me/theorems/c314d0fb-1704-4bc9-b0e1-78496541b347
-- title:
--   Join: map st
-- statement:
--   The Join construction uses the map st property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/TensJoin.lean#L44-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/TensJoin.lean#L44-L63

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

theorem PositivityTheory.ThKR.Join.map_st {A : ι → Type} (act : ∀ i, A i → Module.End ℂ (V i)) (P : Submodule ℂ (⨂[ℂ] i, V i))
    (hP : ∀ i a, ∀ x ∈ P, map (Function.update (fun j => (LinearMap.id : V j →ₗ[ℂ] V j)) i (act i a)) x ∈ P)
    (u : ∀ i, Module.End ℂ (V i)) (hu : ∀ i, u i ∈ Algebra.adjoin ℂ (Set.range (act i))) : ∀ x ∈ P, map u x ∈ P := by sorry
