-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_FK_op_id
-- name    : PositivityTheory.Rg.Sw.LC.FK.op_id
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T08:58:02.049842+00:00
-- url     : https://prove2.me/theorems/ddec1b3f-ff98-4fc5-8f25-240b4130504f
-- title:
--   FK: op id
-- statement:
--   The FK construction uses the op id property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/PderivComm.lean#L80-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/PderivComm.lean#L80-L111

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

theorem PositivityTheory.Rg.Sw.LC.FK.op_id (c : ℝ) (ε : Fin m → Bool) (i j : Fin n) (P : PX m n) :
    (∑ a ∈ Finset.univ.filter (fun a => ε a = true), cr c (a, i, false) (pderiv (a, j, true) P)) -
      ∑ a ∈ Finset.univ.filter (fun a => ε a = false), cr c (a, j, true) (pderiv (a, i, false) P) =
    ((c : ℂ) ^ 2) • mulQ ε i j P - lapS ε c i j P - (c : ℂ) • eulH c i j P + (c : ℂ) • eulA c i j P -
      (if i = j then (c : ℂ) * ∑ a, sgn ε a else 0) • P := by sorry
