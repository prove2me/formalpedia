-- Prove2me | Theorems.Thm_PositivityTheory_RgUd_T_Nil_Orb_BReps_sigma_fin_eq_iff
-- name    : PositivityTheory.RgUd.T.Nil.Orb.BReps.sigma_fin_eq_iff
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T09:02:55.215595+00:00
-- url     : https://prove2.me/theorems/742bd957-e875-40ba-b008-df302b712897
-- title:
--   BReps: sigma fin eq iff
-- statement:
--   The BReps construction uses the sigma fin eq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/CompactOrbits/NilpotentOrbits/OrbitIntegrals/CentralizerRepresentatives/ChainA.lean#L11-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/CompactOrbits/NilpotentOrbits/OrbitIntegrals/CentralizerRepresentatives/ChainA.lean#L11-L18

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

theorem PositivityTheory.RgUd.T.Nil.Orb.BReps.sigma_fin_eq_iff {ι : Type} {l : ι → ℕ} {b a : ι} {j : Fin (l b)} {i : Fin (l a)} :
    (⟨b, j⟩ : Σ a, Fin (l a)) = ⟨a, i⟩ ↔ b = a ∧ (j : ℕ) = i := by sorry
