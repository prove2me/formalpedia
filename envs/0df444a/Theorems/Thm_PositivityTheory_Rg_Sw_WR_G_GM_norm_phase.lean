-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_G_GM_norm_phase
-- name    : PositivityTheory.Rg.Sw.WR.G.GM.norm_phase
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:00:20.269591+00:00
-- url     : https://prove2.me/theorems/776776b1-8777-4984-9cbe-dd5206a2fc1f
-- title:
--   GM: norm phase
-- statement:
--   The GM construction uses the norm phase property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/GaussM.lean#L36-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/GaussM.lean#L36-L42

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

theorem PositivityTheory.Rg.Sw.WR.G.GM.norm_phase {ε : Fin m → Bool} {t : ℝ} {b : Matrix (Fin n) (Fin n) ℂ} (hb : b.IsHermitian)
    (x : Fin m → Fin n → ℂ) : ‖Complex.exp (Complex.I * t * (b * gramX ε x).trace)‖ = 1 := by sorry
