-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_hop_pderiv_cr
-- name    : PositivityTheory.Rg.Sw.LC.hop_pderiv_cr
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T08:57:29.392748+00:00
-- url     : https://prove2.me/theorems/962960d8-dca7-4528-a743-b67a718a6814
-- title:
--   LC: hop pderiv cr
-- statement:
--   The LC construction uses the hop pderiv cr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/HopPderivComm.lean#L38-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/HopPderivComm.lean#L38-L53

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_NullStableAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_HopPderivComm
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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
open PositivityTheory.Rg.Sw
variable {m n : ℕ}

theorem PositivityTheory.Rg.Sw.LC.hop_pderiv_cr (c : ℝ) (j k : Fin m × Fin n × Bool) (Q : PX m n) :
    pderiv k (cr c j Q) = cr c j (pderiv k Q) + C (2 * c : ℂ) * (if k = (j.1, j.2.1, !j.2.2) then Q else 0) := by sorry
