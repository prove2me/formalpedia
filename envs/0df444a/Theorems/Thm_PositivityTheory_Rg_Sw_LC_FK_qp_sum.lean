-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_FK_qp_sum
-- name    : PositivityTheory.Rg.Sw.LC.FK.qp_sum
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:59:40.138015+00:00
-- url     : https://prove2.me/theorems/33b083e5-54d1-504e-a82f-ab47d1cf58bf
-- title:
--   FK: qp sum
-- statement:
--   The FK construction uses the qp sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/PderivComm.lean#L73-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/PderivComm.lean#L73-L78

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

theorem PositivityTheory.Rg.Sw.LC.FK.qp_sum (ε : Fin m → Bool) (i j : Fin n) :
    Qp ε i j = ∑ a, C (sgn ε a) * ((X (a, i, true) : PX m n) * X (a, j, false)) := by sorry
