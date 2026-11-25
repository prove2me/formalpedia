-- Prove2me | Theorems.Thm_PositivityTheory_RgJS_AbsoluteRigidity_rel_remove
-- name    : PositivityTheory.RgJS.AbsoluteRigidity.rel_remove
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T09:02:49.997221+00:00
-- url     : https://prove2.me/theorems/ee2c71a0-8e0b-4cda-ae4b-861730ad04ac
-- title:
--   Absolute Rigidity: rel remove
-- statement:
--   The Absolute Rigidity construction uses the rel remove property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/JacquetShalikaBounds/AbsoluteRigidity/AbsoluteRigidityLemma/AbsoluteRigidityOfCommon.lean#L37-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/JacquetShalikaBounds/AbsoluteRigidity/AbsoluteRigidityLemma/AbsoluteRigidityOfCommon.lean#L37-L43

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_NewtonLow
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_AbsoluteRigidityLemma_AbsoluteRigidityOfCommon
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.RgJS
open PositivityTheory.RgJS.AbsoluteRigidity
variable {W : Type} {q : W → ℕ} {X : Type} {d : X → ℕ} {A : ∀ x, W → Fin (d x) → ℂ}

theorem PositivityTheory.RgJS.AbsoluteRigidity.rel_remove {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] {x : ι → X × ℝ}
    {y : κ → X × ℝ} (h : Rel q A x y) (i : ι) (j : κ) (hij : x i = y j) :
    Rel q A (fun i' : {i' // i' ≠ i} => x i') (fun j' : {j' // j' ≠ j} => y j') := by sorry
