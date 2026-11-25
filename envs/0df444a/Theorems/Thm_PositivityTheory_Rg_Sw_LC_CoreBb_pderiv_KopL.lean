-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreBb_pderiv_KopL
-- name    : PositivityTheory.Rg.Sw.LC.CoreBb.pderiv_KopL
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:56:41.744022+00:00
-- url     : https://prove2.me/theorems/ce852bad-f63f-53f7-bb28-bf22259ff7cd
-- title:
--   Core Bb: pderiv Kop L
-- statement:
--   The Core Bb construction uses the pderiv Kop L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/ProdMapPowSingle.lean#L204-L222
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/ProdMapPowSingle.lean#L204-L222

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

theorem PositivityTheory.Rg.Sw.LC.CoreBb.pderiv_KopL (ε : Fin m → Bool) (i j : Fin n) (k : Fin m × Fin n × Bool) (f : PX m n) :
    pderiv k (KopL ε i j f) = KopL ε i j (pderiv k f) +
      ((if ε k.1 = true ∧ k.2.1 = i ∧ k.2.2 = false then pderiv (k.1, j, false) f else 0) -
        (if ε k.1 = false ∧ k.2.1 = j ∧ k.2.2 = true then pderiv (k.1, i, true) f else 0)) := by sorry
