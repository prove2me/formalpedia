-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_G_GI_add_pow_le
-- name    : PositivityTheory.Rg.Sw.WR.G.GI.add_pow_le
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T09:06:45.171507+00:00
-- url     : https://prove2.me/theorems/9932a2e6-275c-522c-8e8f-0e12a1caeecf
-- title:
--   GI: add pow le
-- statement:
--   The GI construction uses the add pow le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/NormMono.lean#L20-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/NormMono.lean#L20-L31

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GaussS
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_NormMono
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix MvPolynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.G PositivityTheory.Rg.Sw.WR.G.GI
open PositivityTheory.Rg.Sw

theorem PositivityTheory.Rg.Sw.WR.G.GI.add_pow_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (k : ℕ) : (a + b) ^ k ≤ 2 ^ k * (a ^ k + b ^ k) := by sorry
