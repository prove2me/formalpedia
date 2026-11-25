-- Prove2me | Theorems.Thm_PositivityTheory_ThKR_Join_position_st
-- name    : PositivityTheory.ThKR.Join.position_st
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:26:25.717021+00:00
-- url     : https://prove2.me/theorems/08e49893-1863-4ea7-84b2-b89777577d31
-- title:
--   Join: position st
-- statement:
--   The Join construction uses the position st property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/TensJoin.lean#L23-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/TensJoin.lean#L23-L42

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

theorem PositivityTheory.ThKR.Join.position_st {A : ι → Type} (act : ∀ i, A i → Module.End ℂ (V i)) (P : Submodule ℂ (⨂[ℂ] i, V i))
    (hP : ∀ i a, ∀ x ∈ P, map (Function.update (fun j => (LinearMap.id : V j →ₗ[ℂ] V j)) i (act i a)) x ∈ P) (i : ι)
    (u : Module.End ℂ (V i)) (hu : u ∈ Algebra.adjoin ℂ (Set.range (act i))) :
    ∀ x ∈ P, map (Function.update (fun j => (LinearMap.id : V j →ₗ[ℂ] V j)) i u) x ∈ P := by sorry
