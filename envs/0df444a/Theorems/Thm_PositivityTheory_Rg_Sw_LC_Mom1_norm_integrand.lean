-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_Mom1_norm_integrand
-- name    : PositivityTheory.Rg.Sw.LC.Mom1.norm_integrand
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:49:08.080701+00:00
-- url     : https://prove2.me/theorems/52fb629f-47a1-4a7e-882a-7d1358cf4418
-- title:
--   Mom1: norm integrand
-- statement:
--   The Mom1 construction uses the norm integrand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/IntegrableRpowGauss.lean#L10-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/IntegrableRpowGauss.lean#L10-L15

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

theorem PositivityTheory.Rg.Sw.LC.Mom1.norm_integrand (c : ℝ) (p q : ℕ) (z : ℂ) :
    ‖z ^ p * star z ^ q * Complex.exp ((-(c * ‖z‖ ^ 2) : ℝ))‖ =
      ‖z‖ ^ ((p + q : ℕ) : ℝ) * Real.exp (-c * ‖z‖ ^ (2 : ℝ)) := by sorry
