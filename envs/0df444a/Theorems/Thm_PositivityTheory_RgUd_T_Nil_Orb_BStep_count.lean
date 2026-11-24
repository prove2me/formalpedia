-- Prove2me | Theorems.Thm_PositivityTheory_RgUd_T_Nil_Orb_BStep_count
-- name    : PositivityTheory.RgUd.T.Nil.Orb.BStep.count
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:26:48.461904+00:00
-- url     : https://prove2.me/theorems/e4697e85-8533-4607-80e4-5ad0f114fbc8
-- title:
--   BStep: count
-- statement:
--   The BStep construction uses the count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/CompactOrbits/NilpotentOrbits/OrbitIntegrals/ModulusInduction/Imports.lean#L7-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/CompactOrbits/NilpotentOrbits/OrbitIntegrals/ModulusInduction/Imports.lean#L7-L89

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_CompactOrbits_NilpotentOrbits_OrbitIntegrals_ModulusInduction_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory PositivityTheory.RgUd PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.T.Nil.Orb PositivityTheory.RgUd.T.Nil.Orb.BStep
open scoped Pointwise

theorem PositivityTheory.RgUd.T.Nil.Orb.BStep.count {G X : Type*} [Group G] [MulAction G X] (J A : Subgroup G) (hAJ : A ≤ J)
    (hn : ∀ j ∈ J, ∀ a ∈ A, j * a * j⁻¹ ∈ A) (y : X) :
    Nat.card ((fun j : G => j • ((fun a : G => a • y) '' (A : Set G))) '' (J : Set G)) *
      (A ⊓ MulAction.stabilizer G y).relIndex (J ⊓ MulAction.stabilizer G y) = A.relIndex J := by sorry
