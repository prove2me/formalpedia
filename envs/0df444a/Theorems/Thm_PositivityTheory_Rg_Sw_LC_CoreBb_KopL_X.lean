-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreBb_KopL_X
-- name    : PositivityTheory.Rg.Sw.LC.CoreBb.KopL_X
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:56:18.422156+00:00
-- url     : https://prove2.me/theorems/f28bb203-3c92-5c68-8a80-75dc93b65321
-- title:
--   Core Bb: Kop L X
-- statement:
--   The Core Bb construction uses the Kop L X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/ProdMapPowSingle.lean#L178-L194
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/ProdMapPowSingle.lean#L178-L194

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

theorem PositivityTheory.Rg.Sw.LC.CoreBb.KopL_X (ε : Fin m → Bool) (i j : Fin n) (k : Fin m × Fin n × Bool) :
    KopL ε i j (X k) = if ε k.1 then (if k.2.2 = false ∧ k.2.1 = j then X (k.1, i, false) else 0)
      else (if k.2.2 = true ∧ k.2.1 = i then -X (k.1, j, true) else 0) := by sorry
