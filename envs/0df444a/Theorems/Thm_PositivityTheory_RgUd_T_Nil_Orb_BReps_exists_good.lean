-- Prove2me | Theorems.Thm_PositivityTheory_RgUd_T_Nil_Orb_BReps_exists_good
-- name    : PositivityTheory.RgUd.T.Nil.Orb.BReps.exists_good
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T09:03:02.133269+00:00
-- url     : https://prove2.me/theorems/3cf6cb01-2373-45b0-80ee-af96c979cb46
-- title:
--   BReps: exists good
-- statement:
--   The BReps construction uses the exists good property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/CompactOrbits/NilpotentOrbits/OrbitIntegrals/CentralizerRepresentatives/ChainB.lean#L88-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/CompactOrbits/NilpotentOrbits/OrbitIntegrals/CentralizerRepresentatives/ChainB.lean#L88-L115

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

theorem PositivityTheory.RgUd.T.Nil.Orb.BReps.exists_good [FiniteDimensional E W] (N : W →ₗ[E] W) (hN : IsNilpotent N) (v : W) :
    ∃ (ι : Type) (_ : Fintype ι) (l s : ι → ℕ) (B : Module.Basis (Σ a, Fin (l a)) E W), IsChain N l B ∧
      (∀ a, 0 < l a) ∧ (∀ a, s a ≤ l a) ∧ (∀ a b, s a ≤ s b + (l a - l b)) ∧
      v = ∑ a, if h : s a < l a then B ⟨a, ⟨s a, h⟩⟩ else 0 := by sorry
