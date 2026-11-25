-- Prove2me | Theorems.Thm_PositivityTheory_ThKF_Unit_ker_le
-- name    : PositivityTheory.ThKF.Unit.ker_le
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:18:41.367532+00:00
-- url     : https://prove2.me/theorems/280839d6-3990-5d21-a83a-30239c0ba622
-- title:
--   Unit: ker le
-- statement:
--   The Unit construction uses the ker le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/CartanFactorisation/TensMax.lean#L12-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/CartanFactorisation/TensMax.lean#L12-L44

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

theorem PositivityTheory.ThKF.Unit.ker_le (K : ∀ i, Submodule ℂ (V i)) (R : Submodule ℂ (⨂[ℂ] i, V i)) (hR : ∀ (f : ∀ i, V i) i, f i ∈ K i → tprod ℂ f ∈ R) :
    LinearMap.ker (map fun i => (K i).mkQ) ≤ R := by sorry
