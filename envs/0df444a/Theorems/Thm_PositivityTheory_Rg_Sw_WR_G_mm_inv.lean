-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_G_mm_inv
-- name    : PositivityTheory.Rg.Sw.WR.G.mm_inv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:50:25.453168+00:00
-- url     : https://prove2.me/theorems/e23a106b-b662-4138-8a3e-ec86946a0ed3
-- title:
--   G: mm inv
-- statement:
--   The G construction uses the mm inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/GaussM.lean#L148-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/GaussM.lean#L148-L155

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

theorem PositivityTheory.Rg.Sw.WR.G.mm_inv (ε : Fin m → Bool) (s : ℝ) (y : E n) (a : Fin m) :
    (GM.Mm ε s (herm y) a)⁻¹ = if ε a then uM (s : ℂ) y else vM (s : ℂ) y := by sorry
