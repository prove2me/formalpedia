-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreBb_symK_inr
-- name    : PositivityTheory.Rg.Sw.LC.CoreBb.symK_inr
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:56:08.704326+00:00
-- url     : https://prove2.me/theorems/72e1d9cb-a7e4-456d-aafd-0343c203921a
-- title:
--   Core Bb: sym K inr
-- statement:
--   The Core Bb construction uses the sym K inr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/ProdMapPowSingle.lean#L238-L241
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/ProdMapPowSingle.lean#L238-L241

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

theorem PositivityTheory.Rg.Sw.LC.CoreBb.symK_inr (ε : Fin m → Bool) (i j : Fin n) (k : Fin m × Fin n × Bool) :
    symK ε i j (X (Sum.inr k)) = if ε k.1 then (if k.2.2 = false ∧ k.2.1 = i then -X (Sum.inr (k.1, j, false)) else 0)
      else (if k.2.2 = true ∧ k.2.1 = j then X (Sum.inr (k.1, i, true)) else 0) := by sorry
