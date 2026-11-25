-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_FK_pderiv_cr
-- name    : PositivityTheory.Rg.Sw.LC.FK.pderiv_cr
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T09:01:40.443019+00:00
-- url     : https://prove2.me/theorems/d71afc40-15ec-5b20-a76d-59a46199db1e
-- title:
--   FK: pderiv cr
-- statement:
--   The FK construction uses the pderiv cr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/PderivComm.lean#L36-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/PderivComm.lean#L36-L43

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

theorem PositivityTheory.Rg.Sw.LC.FK.pderiv_cr (c : ℝ) (k k' : Fin m × Fin n × Bool) (Q : PX m n) :
    pderiv (sw k') (cr c k Q) = cr c k (pderiv (sw k') Q) + (if k = k' then (2 * c : ℂ) else 0) • Q := by sorry
