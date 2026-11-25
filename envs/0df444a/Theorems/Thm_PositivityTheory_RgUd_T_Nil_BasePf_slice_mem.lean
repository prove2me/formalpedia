-- Prove2me | Theorems.Thm_PositivityTheory_RgUd_T_Nil_BasePf_slice_mem
-- name    : PositivityTheory.RgUd.T.Nil.BasePf.slice_mem
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:02:37.755015+00:00
-- url     : https://prove2.me/theorems/81bef216-093a-5dca-a97a-2f9dc40abb8b
-- title:
--   Base Pf: slice mem
-- statement:
--   The Base Pf construction uses the slice mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/CompactOrbits/NilpotentOrbits/BaseOrbits/PieceMem.lean#L47-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/CompactOrbits/NilpotentOrbits/BaseOrbits/PieceMem.lean#L47-L51

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

theorem PositivityTheory.RgUd.T.Nil.BasePf.slice_mem {F : Y × W → ℂ} (hF : F ∈ TF (Y × W)) (w : W) : (fun y => F (y, w)) ∈ TF Y := by sorry
