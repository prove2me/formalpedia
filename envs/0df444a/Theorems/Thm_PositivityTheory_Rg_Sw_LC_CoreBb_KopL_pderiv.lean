-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreBb_KopL_pderiv
-- name    : PositivityTheory.Rg.Sw.LC.CoreBb.KopL_pderiv
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:56:25.398859+00:00
-- url     : https://prove2.me/theorems/c02438a8-7e3a-5b7f-ad90-74e0c9a86321
-- title:
--   Core Bb: Kop L pderiv
-- statement:
--   The Core Bb construction uses the Kop L pderiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/ProdMapPowSingle.lean#L224-L231
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/ProdMapPowSingle.lean#L224-L231

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_CoreSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_ProdMapPowSingle
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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.CoreBb
open PositivityTheory.Rg.Sw
variable {m n : ℕ}

theorem PositivityTheory.Rg.Sw.LC.CoreBb.KopL_pderiv (ε : Fin m → Bool) (i j : Fin n) (k : Fin m × Fin n × Bool) (f : PX m n) :
    KopL ε i j (pderiv k f) - pderiv k (KopL ε i j f) =
      if ε k.1 then (if k.2.2 = false ∧ k.2.1 = i then -pderiv (k.1, j, false) f else 0)
      else (if k.2.2 = true ∧ k.2.1 = j then pderiv (k.1, i, true) f else 0) := by sorry
