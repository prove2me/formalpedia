-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_FK_kopL_apply
-- name    : PositivityTheory.Rg.Sw.LC.FK.kopL_apply
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:57:59.599579+00:00
-- url     : https://prove2.me/theorems/fa54f240-2b06-4148-9ec0-7f5c4316e1ea
-- title:
--   FK: kop L apply
-- statement:
--   The FK construction uses the kop L apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/PderivComm.lean#L113-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/PderivComm.lean#L113-L116

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

theorem PositivityTheory.Rg.Sw.LC.FK.kopL_apply (ε : Fin m → Bool) (i j : Fin n) (p : PX m n) :
    KopL ε i j p = ∑ a ∈ Finset.univ.filter (fun a => ε a = true), (X (a, i, false) : PX m n) * pderiv (a, j, false) p -
      ∑ a ∈ Finset.univ.filter (fun a => ε a = false), (X (a, j, true) : PX m n) * pderiv (a, i, true) p := by sorry
