-- Prove2me | Theorems.Thm_PositivityTheory_RgJS_AbsoluteRigidity_exists_common
-- name    : PositivityTheory.RgJS.AbsoluteRigidity.exists_common
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T09:02:55.159168+00:00
-- url     : https://prove2.me/theorems/064a5ae7-7d86-5f7b-a409-33b13dd9c5a3
-- title:
--   Absolute Rigidity: exists common
-- statement:
--   The Absolute Rigidity construction uses the exists common property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/JacquetShalikaBounds/AbsoluteRigidity/AbsoluteRigidityLemma/AbsoluteRigidityOfCommon.lean#L45-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/JacquetShalikaBounds/AbsoluteRigidity/AbsoluteRigidityLemma/AbsoluteRigidityOfCommon.lean#L45-L78

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

theorem PositivityTheory.RgJS.AbsoluteRigidity.exists_common (hC : Common0) (hS : Sys q X d A) {ι κ : Type} [Fintype ι] [Fintype κ]
    (x : ι → X × ℝ) (y : κ → X × ℝ) (h : Rel q A x y) (hne : Nonempty ι ∨ Nonempty κ) :
    ∃ i j, x i = y j := by sorry
