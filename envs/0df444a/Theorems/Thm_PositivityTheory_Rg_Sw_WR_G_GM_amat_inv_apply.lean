-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_G_GM_amat_inv_apply
-- name    : PositivityTheory.Rg.Sw.WR.G.GM.amat_inv_apply
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T09:04:04.075132+00:00
-- url     : https://prove2.me/theorems/e8547848-d010-5904-9e06-4319c59345d1
-- title:
--   GM: amat inv apply
-- statement:
--   The GM construction uses the amat inv apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/GaussM.lean#L125-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/GaussM.lean#L125-L134

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

theorem PositivityTheory.Rg.Sw.WR.G.GM.amat_inv_apply (ε : Fin m → Bool) {c : ℝ} (hc : c ≠ 0) (s : ℝ) {b : Matrix (Fin n) (Fin n) ℂ}
    (hb : b.IsHermitian) (a : Fin m) (i j : Fin n) :
    (Amat ε c (s * c) b a)⁻¹ j i = (c : ℂ)⁻¹ * ((Mm ε s b a)⁻¹) i j := by sorry
