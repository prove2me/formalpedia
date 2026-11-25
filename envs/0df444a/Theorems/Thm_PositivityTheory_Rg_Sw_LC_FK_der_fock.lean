-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_FK_der_fock
-- name    : PositivityTheory.Rg.Sw.LC.FK.der_fock
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:58:25.589114+00:00
-- url     : https://prove2.me/theorems/4eda45a6-6fb6-42bb-abca-011a926731b2
-- title:
--   FK: der fock
-- statement:
--   The FK construction uses the der fock property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/PderivComm.lean#L56-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/PderivComm.lean#L56-L71

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_NullStableAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PderivComm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.FK
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
variable {m n : ℕ}

theorem PositivityTheory.Rg.Sw.LC.FK.der_fock (hB : FockBasic) (c : ℝ) (hc : 0 < c) (k : Fin m × Fin n × Bool) (p : PX m n) :
    pderiv (sw k) (fock c p) = (2 * c : ℂ) • fock c (pderiv k p) := by sorry
