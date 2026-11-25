-- Prove2me | Theorems.Thm_PositivityTheory_RgUd_T_Nil_BasePf_piece_mem
-- name    : PositivityTheory.RgUd.T.Nil.BasePf.piece_mem
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:02:45.14167+00:00
-- url     : https://prove2.me/theorems/8f363ce3-1cb5-453c-b147-3244fbf3bfeb
-- title:
--   Base Pf: piece mem
-- statement:
--   The Base Pf construction uses the piece mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/CompactOrbits/NilpotentOrbits/BaseOrbits/PieceMem.lean#L55-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/CompactOrbits/NilpotentOrbits/BaseOrbits/PieceMem.lean#L55-L74

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerLSpace
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_CompactOrbits_NilpotentOrbits_BaseOrbits_PieceMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Set GroundTheory.Automorphic.Whittaker
open PositivityTheory PositivityTheory.RgUd PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.T.Nil.BasePf
variable {Y W G : Type*} [TopologicalSpace Y] [T2Space Y] [TopologicalSpace W] [T2Space W]
  [Group G] [MulAction G W]
open Classical

theorem PositivityTheory.RgUd.T.Nil.BasePf.piece_mem (K : Subgroup G) (S : Set W) (hKo : ∀ w ∈ S, IsOpen {w' | ∃ g ∈ K, g • w = w'})
    {F : Y × W → ℂ} (hF : F ∈ TF (Y × W)) (hFS : ∀ p : Y × W, p.2 ∉ S → F p = 0)
    (q : Quotient (rel K)) :
    (fun p : Y × W => F p * if Quotient.mk (rel K) p.2 = q then 1 else 0) ∈ TF (Y × W) := by sorry
