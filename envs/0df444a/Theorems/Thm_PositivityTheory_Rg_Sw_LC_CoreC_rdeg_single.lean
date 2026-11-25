-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_rdeg_single
-- name    : PositivityTheory.Rg.Sw.LC.CoreC.rdeg_single
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:57:06.44618+00:00
-- url     : https://prove2.me/theorems/4e23c2cb-a620-43ab-89fd-f3c40b41af07
-- title:
--   Core C: rdeg single
-- statement:
--   The Core C construction uses the rdeg single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/CoeffSmulX.lean#L53-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/CoeffSmulX.lean#L53-L69

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_BfSmulRight
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_CoeffSmulX
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finsupp
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
open PositivityTheory.Rg.Sw.LC.CoreC
open PositivityTheory.Rg.Sw G
variable {m n : ℕ}

theorem PositivityTheory.Rg.Sw.LC.CoreC.rdeg_single (ε : Fin m → Bool) (k : Fin m × Fin n × Bool) (hk : inF1 ε k) :
    rdeg ε (Finsupp.single k 1) = fun a => if a = k.1 then 1 else 0 := by sorry
