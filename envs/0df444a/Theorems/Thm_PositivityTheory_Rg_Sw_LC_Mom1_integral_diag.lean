-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_Mom1_integral_diag
-- name    : PositivityTheory.Rg.Sw.LC.Mom1.integral_diag
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:48:47.509531+00:00
-- url     : https://prove2.me/theorems/d29cc050-4503-4da4-a3eb-55e23fa8b0e7
-- title:
--   Mom1: integral diag
-- statement:
--   The Mom1 construction uses the integral diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/IntegrableRpowGauss.lean#L41-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/IntegrableRpowGauss.lean#L41-L61

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_OneMom
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_IntegrableRpowGauss
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Real
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.Mom1

theorem PositivityTheory.Rg.Sw.LC.Mom1.integral_diag (c : ℝ) (hc : 0 < c) (p : ℕ) :
    ∫ z : ℂ, z ^ p * star z ^ p * Complex.exp ((-(c * ‖z‖ ^ 2) : ℝ)) =
      ((Real.pi * (p.factorial : ℝ) / c ^ (p + 1) : ℝ) : ℂ) := by sorry
