-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_word_sum
-- name    : PositivityTheory.Rg.Sw.WR.K.GB.word_sum
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T09:02:11.29509+00:00
-- url     : https://prove2.me/theorems/01c67517-2f89-43af-8bf2-020df1fb7275
-- title:
--   GB: word sum
-- statement:
--   The GB construction uses the word sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/GBLink.lean#L161-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/GBLink.lean#L161-L171

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainBSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GBLink
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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.K PositivityTheory.Rg.Sw.WR.K.GB
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
variable {F G : Mc n → ℂ} {U : Set (Mc n)}

theorem PositivityTheory.Rg.Sw.WR.K.GB.word_sum {ι : Type} (s : Finset ι) (c : ι → ℂ) (f : ι → Mc n → ℂ) (L : List (Fin n × Fin n))
    (hU : IsOpen U) (hf : ∀ t, ContDiffOn ℂ (⊤ : ℕ∞) (f t) U) :
    Set.EqOn (word L (fun x => ∑ t ∈ s, c t * f t x)) (fun x => ∑ t ∈ s, c t * word L (f t) x) U := by sorry
