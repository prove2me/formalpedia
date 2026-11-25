-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_G_GM_det_ne_zero
-- name    : PositivityTheory.Rg.Sw.WR.G.GM.det_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:51:03.011087+00:00
-- url     : https://prove2.me/theorems/2ce35dfd-ed6f-4705-bed6-16dd096282b6
-- title:
--   GM: det ne zero
-- statement:
--   The GM construction uses the det ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/GaussM.lean#L85-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/GaussM.lean#L85-L108

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

theorem PositivityTheory.Rg.Sw.WR.G.GM.det_ne_zero {b : Matrix (Fin n) (Fin n) ℂ} (hb : b.IsHermitian) (r : ℝ) :
    (1 - (Complex.I * r) • b).det ≠ 0 := by sorry
