-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_eqOn_word
-- name    : PositivityTheory.Rg.Sw.WR.K.GB.eqOn_word
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:51:52.144161+00:00
-- url     : https://prove2.me/theorems/70a3be79-c4e1-4999-9781-8e3434a7379f
-- title:
--   GB: eq On word
-- statement:
--   The GB construction uses the eq On word property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/GBLink.lean#L134-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/GBLink.lean#L134-L138

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

theorem PositivityTheory.Rg.Sw.WR.K.GB.eqOn_word (L : List (Fin n × Fin n)) (hU : IsOpen U) {H H' : Mc n → ℂ} (h : Set.EqOn H H' U) :
    Set.EqOn (word L H) (word L H') U := by sorry
