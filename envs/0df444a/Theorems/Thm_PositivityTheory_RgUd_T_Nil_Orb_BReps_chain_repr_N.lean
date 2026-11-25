-- Prove2me | Theorems.Thm_PositivityTheory_RgUd_T_Nil_Orb_BReps_chain_repr_N
-- name    : PositivityTheory.RgUd.T.Nil.Orb.BReps.chain_repr_N
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T09:03:03.619194+00:00
-- url     : https://prove2.me/theorems/d281a726-8ea3-43e3-9e9c-828cb63b9c63
-- title:
--   BReps: chain repr N
-- statement:
--   The BReps construction uses the chain repr N property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/CompactOrbits/NilpotentOrbits/OrbitIntegrals/CentralizerRepresentatives/ChainA.lean#L20-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/CompactOrbits/NilpotentOrbits/OrbitIntegrals/CentralizerRepresentatives/ChainA.lean#L20-L58

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_CompactOrbits_NilpotentOrbits_OrbitIntegrals_CentralizerRepresentatives_IsChain
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_CompactOrbits_NilpotentOrbits_OrbitIntegrals_CentralizerRepresentatives_ChainA
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
variable {E W : Type} [Field E] [AddCommGroup W] [Module E W]

theorem PositivityTheory.RgUd.T.Nil.Orb.BReps.chain_repr_N {N : W →ₗ[E] W} {ι : Type} {l : ι → ℕ} {B : Module.Basis (Σ a, Fin (l a)) E W}
    (hB : IsChain N l B) (z : W) (a : ι) (i : Fin (l a)) :
    B.repr (N z) ⟨a, i⟩ = if h : 0 < (i : ℕ) then B.repr z ⟨a, ⟨i - 1, by omega⟩⟩ else 0 := by sorry
