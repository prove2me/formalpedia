-- Prove2me | Theorems.Thm_PositivityTheory_RgUd_T_Nil_BasePf_rel_iff
-- name    : PositivityTheory.RgUd.T.Nil.BasePf.rel_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:54:23.276832+00:00
-- url     : https://prove2.me/theorems/c9190596-2099-4135-b499-9e39151f4b91
-- title:
--   Base Pf: rel iff
-- statement:
--   The Base Pf construction uses the rel iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/CompactOrbits/NilpotentOrbits/BaseOrbits/PieceMem.lean#L20-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/CompactOrbits/NilpotentOrbits/BaseOrbits/PieceMem.lean#L20-L22

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

theorem PositivityTheory.RgUd.T.Nil.BasePf.rel_iff (K : Subgroup G) (a b : W) :
    Quotient.mk (rel K) a = Quotient.mk (rel K) b ↔ ∃ g ∈ K, g • b = a := by sorry
