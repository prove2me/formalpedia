-- Prove2me | Theorems.Thm_PositivityTheory_RgUd_T_Nil_Orb_BReps_cb_init
-- name    : PositivityTheory.RgUd.T.Nil.Orb.BReps.cb_init
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T09:03:01.488578+00:00
-- url     : https://prove2.me/theorems/7f29db05-c1a8-4e66-9542-c7d12cfec0f9
-- title:
--   BReps: cb init
-- statement:
--   The BReps construction uses the cb init property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/CompactOrbits/NilpotentOrbits/OrbitIntegrals/CentralizerRepresentatives/CbExistsChainOfGen.lean#L93-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/CompactOrbits/NilpotentOrbits/OrbitIntegrals/CentralizerRepresentatives/CbExistsChainOfGen.lean#L93-L113

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

theorem PositivityTheory.RgUd.T.Nil.Orb.BReps.cb_init (N : W →ₗ[E] W) {ι : Type} [Fintype ι] {l : ι → ℕ}
    (B0 : Module.Basis (Σ a, Fin (l a)) E W) (hB0 : IsChain N l B0) (hl : ∀ a, 0 < l a) (v : W) :
    ∃ (y : ι → W) (s : ι → ℕ), (∀ a, (N ^ l a) (y a) = 0) ∧
      (∀ a, B0 ⟨a, ⟨0, hl a⟩⟩ ∈ span E (Set.range (cbFam N l y)) ⊔ LinearMap.range N) ∧
      (∀ a, s a ≤ l a) ∧ v = ∑ a, (N ^ s a) (y a) := by sorry
