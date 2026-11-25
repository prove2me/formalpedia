-- Prove2me | Theorems.Thm_PositivityTheory_RgUd_T_Nil_Orb_BReps_cb_single
-- name    : PositivityTheory.RgUd.T.Nil.Orb.BReps.cb_single
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T09:03:15.395485+00:00
-- url     : https://prove2.me/theorems/424ae7c5-0dfd-4c28-90ea-f4e20efda7cf
-- title:
--   BReps: cb single
-- statement:
--   The BReps construction uses the cb single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/CompactOrbits/NilpotentOrbits/OrbitIntegrals/CentralizerRepresentatives/CbExistsChainOfGen.lean#L45-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/CompactOrbits/NilpotentOrbits/OrbitIntegrals/CentralizerRepresentatives/CbExistsChainOfGen.lean#L45-L91

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_CompactOrbits_NilpotentOrbits_OrbitIntegrals_CentralizerRepresentatives_CbIsChainApply
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_CompactOrbits_NilpotentOrbits_OrbitIntegrals_CentralizerRepresentatives_CbExistsChainOfGen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.RgUd PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.T.Nil.Orb PositivityTheory.RgUd.T.Nil.Orb.BReps
open Module Submodule
variable {E W : Type} [Field E] [AddCommGroup W] [Module E W]

theorem PositivityTheory.RgUd.T.Nil.Orb.BReps.cb_single (N : W →ₗ[E] W) (L : ℕ) (u : W) (hu : (N ^ L) u = 0) (c : Fin L → E) :
    ∃ s ≤ L, ∃ y : W, (N ^ L) y = 0 ∧ (N ^ s) y = ∑ i, c i • (N ^ (i : ℕ)) u ∧
      u ∈ span E {y} ⊔ LinearMap.range N := by sorry
