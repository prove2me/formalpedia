-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_X_pderiv_mono
-- name    : PositivityTheory.Rg.Sw.LC.CoreC.X_pderiv_mono
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:57:18.593086+00:00
-- url     : https://prove2.me/theorems/6c9dbdb8-bea3-45e9-80a0-8e93841a22f1
-- title:
--   Core C: X pderiv mono
-- statement:
--   The Core C construction uses the X pderiv mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/XPderivMono.lean#L62-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/XPderivMono.lean#L62-L68

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_ContractionFirstOperatorAdjoint
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_XPderivMono
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finsupp
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
open PositivityTheory.Rg.Sw.LC.CoreC
open PositivityTheory.Rg.Sw G
variable {m n : ℕ}

theorem PositivityTheory.Rg.Sw.LC.CoreC.X_pderiv_mono (k : Fin m × Fin n × Bool) (v : Fin m × Fin n × Bool →₀ ℕ) :
    (X k * pderiv k (monomial v (1 : ℂ)) : PX m n) = ((v k : ℕ) : ℂ) • monomial v 1 := by sorry
