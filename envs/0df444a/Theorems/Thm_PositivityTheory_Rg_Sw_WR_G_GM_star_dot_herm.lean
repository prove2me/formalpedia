-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_G_GM_star_dot_herm
-- name    : PositivityTheory.Rg.Sw.WR.G.GM.star_dot_herm
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:01:20.127526+00:00
-- url     : https://prove2.me/theorems/740d64b3-54fe-4138-8eb5-44139ee9fa1d
-- title:
--   GM: star dot herm
-- statement:
--   The GM construction uses the star dot herm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/GaussM.lean#L77-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/GaussM.lean#L77-L83

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GaussS
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GaussM
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
open scoped ComplexOrder
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.G
open PositivityTheory.Rg.Sw
variable {m n : ℕ}
open PositivityTheory.Rg.Sw.WR.G.GM

theorem PositivityTheory.Rg.Sw.WR.G.GM.star_dot_herm {b : Matrix (Fin n) (Fin n) ℂ} (hb : b.IsHermitian) (v : Fin n → ℂ) :
    star (star v ⬝ᵥ (b *ᵥ v)) = star v ⬝ᵥ (b *ᵥ v) := by sorry
