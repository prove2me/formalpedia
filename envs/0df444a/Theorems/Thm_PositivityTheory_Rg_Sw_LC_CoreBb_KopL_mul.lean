-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreBb_KopL_mul
-- name    : PositivityTheory.Rg.Sw.LC.CoreBb.KopL_mul
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:56:11.261006+00:00
-- url     : https://prove2.me/theorems/a4765291-26cd-41ec-8ba2-20c04163dbf2
-- title:
--   Core Bb: Kop L mul
-- statement:
--   The Core Bb construction uses the Kop L mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/ProdMapPowSingle.lean#L196-L202
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/ProdMapPowSingle.lean#L196-L202

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

theorem PositivityTheory.Rg.Sw.LC.CoreBb.KopL_mul (ε : Fin m → Bool) (i j : Fin n) (g h : PX m n) :
    KopL ε i j (g * h) = KopL ε i j g * h + g * KopL ε i j h := by sorry
