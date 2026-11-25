-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_Mom1_integral_offdiag
-- name    : PositivityTheory.Rg.Sw.LC.Mom1.integral_offdiag
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:48:50.906559+00:00
-- url     : https://prove2.me/theorems/8615f9bd-d6ee-4b2a-a3d6-aea16609deac
-- title:
--   Mom1: integral offdiag
-- statement:
--   The Mom1 construction uses the integral offdiag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/IntegrableRpowGauss.lean#L63-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/IntegrableRpowGauss.lean#L63-L107

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

theorem PositivityTheory.Rg.Sw.LC.Mom1.integral_offdiag (c : ℝ) (p q : ℕ) (hpq : p ≠ q) :
    ∫ z : ℂ, z ^ p * star z ^ q * Complex.exp ((-(c * ‖z‖ ^ 2) : ℝ)) = 0 := by sorry
