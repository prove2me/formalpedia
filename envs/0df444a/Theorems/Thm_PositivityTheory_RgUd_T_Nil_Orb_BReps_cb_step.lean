-- Prove2me | Theorems.Thm_PositivityTheory_RgUd_T_Nil_Orb_BReps_cb_step
-- name    : PositivityTheory.RgUd.T.Nil.Orb.BReps.cb_step
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T09:03:21.204815+00:00
-- url     : https://prove2.me/theorems/0eabf9e3-6cd4-5796-b291-14818e636ac0
-- title:
--   BReps: cb step
-- statement:
--   The BReps construction uses the cb step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/CompactOrbits/NilpotentOrbits/OrbitIntegrals/CentralizerRepresentatives/ChainB.lean#L14-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/CompactOrbits/NilpotentOrbits/OrbitIntegrals/CentralizerRepresentatives/ChainB.lean#L14-L86

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_CompactOrbits_NilpotentOrbits_OrbitIntegrals_CentralizerRepresentatives_CbExistsChainOfGen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsChainsOfRange
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_CompactOrbits_NilpotentOrbits_OrbitIntegrals_CentralizerRepresentatives_ChainB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PositivityTheory PositivityTheory.RgUd PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.T.Nil.Orb PositivityTheory.RgUd.T.Nil.Orb.BReps
open Module Submodule
variable {E W : Type} [Field E] [AddCommGroup W] [Module E W]

theorem PositivityTheory.RgUd.T.Nil.Orb.BReps.cb_step (N : W →ₗ[E] W) (hN : IsNilpotent N) {ι : Type} [Fintype ι] [DecidableEq ι] {l : ι → ℕ}
    (hl : ∀ a, 0 < l a) (v : W) (y : ι → W) (s : ι → ℕ) (hy0 : ∀ a, (N ^ l a) (y a) = 0)
    (B : Module.Basis (Σ a, Fin (l a)) E W) (hB : IsChain N l B) (hBy : ∀ p, B p = cbFam N l y p)
    (hs : ∀ a, s a ≤ l a) (hv : v = ∑ a, (N ^ s a) (y a)) (a b : ι) (hab : s b + (l a - l b) < s a) :
    ∃ (y' : ι → W) (s' : ι → ℕ), (∀ a, (N ^ l a) (y' a) = 0) ∧
      (∃ B' : Module.Basis (Σ a, Fin (l a)) E W, IsChain N l B' ∧ ∀ p, B' p = cbFam N l y' p) ∧
      (∀ a, s' a ≤ l a) ∧ v = ∑ a, (N ^ s' a) (y' a) ∧ ∑ a, s' a < ∑ a, s a := by sorry
