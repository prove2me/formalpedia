-- Prove2me | Theorems.Thm_PositivityTheory_RgJS_AbsoluteRigidity_main
-- name    : PositivityTheory.RgJS.AbsoluteRigidity.main
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T09:02:33.208071+00:00
-- url     : https://prove2.me/theorems/da4ebb97-5a98-402b-be5a-84c02250a64d
-- title:
--   Absolute Rigidity: main
-- statement:
--   The Absolute Rigidity construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/JacquetShalikaBounds/AbsoluteRigidity/AbsoluteRigidityLemma/AbsoluteRigidityOfCommon.lean#L80-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/JacquetShalikaBounds/AbsoluteRigidity/AbsoluteRigidityLemma/AbsoluteRigidityOfCommon.lean#L80-L113

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

theorem PositivityTheory.RgJS.AbsoluteRigidity.main (hC : Common0) (hS : Sys q X d A) : ∀ (N : ℕ) (ι κ : Type) [Fintype ι] [Fintype κ]
    (x : ι → X × ℝ) (y : κ → X × ℝ), Fintype.card ι + Fintype.card κ ≤ N → Rel q A x y →
      ∃ s : ι ≃ κ, ∀ i, x i = y (s i) := by sorry
