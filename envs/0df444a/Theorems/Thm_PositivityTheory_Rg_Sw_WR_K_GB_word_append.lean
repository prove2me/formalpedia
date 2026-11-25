-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_word_append
-- name    : PositivityTheory.Rg.Sw.WR.K.GB.word_append
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:49:59.340059+00:00
-- url     : https://prove2.me/theorems/f4d18951-af82-4629-87d9-1e9795865ea3
-- title:
--   GB: word append
-- statement:
--   The GB construction uses the word append property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/GBLink.lean#L173-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/GBLink.lean#L173-L175

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

theorem PositivityTheory.Rg.Sw.WR.K.GB.word_append (L₁ L₂ : List (Fin n × Fin n)) (H : Mc n → ℂ) :
    word (L₁ ++ L₂) H = word L₁ (word L₂ H) := by sorry
