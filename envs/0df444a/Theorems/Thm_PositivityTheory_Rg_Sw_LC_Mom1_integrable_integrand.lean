-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_Mom1_integrable_integrand
-- name    : PositivityTheory.Rg.Sw.LC.Mom1.integrable_integrand
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:48:55.48591+00:00
-- url     : https://prove2.me/theorems/02e2ec55-d7c4-41ee-8a5d-63b957087f39
-- title:
--   Mom1: integrable integrand
-- statement:
--   The Mom1 construction uses the integrable integrand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/IntegrableRpowGauss.lean#L35-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/IntegrableRpowGauss.lean#L35-L39

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

theorem PositivityTheory.Rg.Sw.LC.Mom1.integrable_integrand (c : ℝ) (hc : 0 < c) (p q : ℕ) :
    Integrable (fun z : ℂ => z ^ p * star z ^ q * Complex.exp ((-(c * ‖z‖ ^ 2) : ℝ))) := by sorry
