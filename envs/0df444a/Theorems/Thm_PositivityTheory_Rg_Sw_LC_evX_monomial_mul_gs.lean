-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_evX_monomial_mul_gs
-- name    : PositivityTheory.Rg.Sw.LC.evX_monomial_mul_gs
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:46:19.558804+00:00
-- url     : https://prove2.me/theorems/2646532c-18bf-42dd-8f77-d559c629b0d6
-- title:
--   LC: ev X monomial mul gs
-- statement:
--   The LC construction uses the ev X monomial mul gs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/IntegrableMonomial.lean#L26-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/IntegrableMonomial.lean#L26-L50

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_NullStableAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_OneMom
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_IntegrableMonomial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial MeasureTheory
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
open PositivityTheory.Rg.Sw
variable {m n : ℕ}

theorem PositivityTheory.Rg.Sw.LC.evX_monomial_mul_gs (c : ℝ) (s : Fin m × Fin n × Bool →₀ ℕ) (r : ℂ) (x : Fin m → Fin n → ℂ) :
    evX (monomial s r) x * gs c x = r * ∏ a, ∏ i, fac c s a i (x a i) := by sorry
