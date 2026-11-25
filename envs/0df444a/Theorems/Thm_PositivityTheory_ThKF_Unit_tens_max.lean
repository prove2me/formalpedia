-- Prove2me | Theorems.Thm_PositivityTheory_ThKF_Unit_tens_max
-- name    : PositivityTheory.ThKF.Unit.tens_max
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:18:29.371129+00:00
-- url     : https://prove2.me/theorems/bb6d3602-06d5-598c-8ac6-cbe916f02c28
-- title:
--   Unit: tens max
-- statement:
--   The Unit construction uses the tens max property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/CartanFactorisation/TensMax.lean#L46-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/CartanFactorisation/TensMax.lean#L46-L81

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_Tensor
import Definitions.Def_Development_WeilBound_ThetaLifts_CartanFactorisation_TensMax
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
open PositivityTheory PositivityTheory.ThKF PositivityTheory.ThKF.Unit
variable {ι : Type} [Fintype ι] [DecidableEq ι] {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]

theorem PositivityTheory.ThKF.Unit.tens_max {A : ι → Type} (act : ∀ i, A i → Module.End ℂ (V i)) (K : ∀ i, Submodule ℂ (V i))
    (hr : ∀ i, Module.rank ℂ (V i) ≤ Cardinal.aleph0) (h1 : ∀ i, K i ≠ ⊤) (h2 : ∀ i a, ∀ x ∈ K i, act i a x ∈ K i)
    (h3 : ∀ i N, K i ≤ N → (∀ a, ∀ x ∈ N, act i a x ∈ N) → N = K i ∨ N = ⊤)
    (R : Submodule ℂ (⨂[ℂ] i, V i)) (hR : ∀ (f : ∀ i, V i) i, f i ∈ K i → tprod ℂ f ∈ R) (P : Submodule ℂ (⨂[ℂ] i, V i))
    (hRP : R ≤ P)
    (hP : ∀ i a, ∀ x ∈ P, map (Function.update (fun j => (LinearMap.id : V j →ₗ[ℂ] V j)) i (act i a)) x ∈ P) :
    P ≤ R ∨ P = ⊤ := by sorry
