-- Prove2me | Theorems.Thm_PositivityTheory_ThKR_Join_tens_join
-- name    : PositivityTheory.ThKR.Join.tens_join
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:24:30.428337+00:00
-- url     : https://prove2.me/theorems/6324d31f-cc02-4473-8847-c38452364243
-- title:
--   Join: tens join
-- statement:
--   The Join construction uses the tens join property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/TensJoin.lean#L65-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/TensJoin.lean#L65-L140

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

theorem PositivityTheory.ThKR.Join.tens_join {A : ι → Type} (act : ∀ i, A i → Module.End ℂ (V i)) (K Z : ∀ i, Submodule ℂ (V i))
    (hr : ∀ i, Module.rank ℂ (V i) ≤ Cardinal.aleph0) (h1 : ∀ i, K i ≠ ⊤) (h2 : ∀ i a, ∀ x ∈ K i, act i a x ∈ K i)
    (h3 : ∀ i N, K i ≤ N → (∀ a, ∀ x ∈ N, act i a x ∈ N) → N = K i ∨ N = ⊤) (v : ∀ i, V i)
    (h4 : ∀ i (t : List (V i)), (∀ x ∈ t, x ∈ K i) → ∀ y,
      ∃ u ∈ Algebra.adjoin ℂ (Set.range (act i)), u (v i) - y ∈ Z i ∧ ∀ x ∈ t, u x ∈ Z i)
    (P P' : Submodule ℂ (⨂[ℂ] i, V i)) (hZ : ∀ (f : ∀ i, V i) i, f i ∈ Z i → tprod ℂ f ∈ P)
    (hZ' : ∀ (f : ∀ i, V i) i, f i ∈ Z i → tprod ℂ f ∈ P')
    (hP : ∀ i a, ∀ x ∈ P, map (Function.update (fun j => (LinearMap.id : V j →ₗ[ℂ] V j)) i (act i a)) x ∈ P)
    (hP' : ∀ i a, ∀ x ∈ P', map (Function.update (fun j => (LinearMap.id : V j →ₗ[ℂ] V j)) i (act i a)) x ∈ P')
    (e : P ⊔ P' = ⊤) : P = ⊤ ∨ P' = ⊤ := by sorry
