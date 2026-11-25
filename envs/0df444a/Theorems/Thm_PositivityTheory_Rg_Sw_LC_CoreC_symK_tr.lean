-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_symK_tr
-- name    : PositivityTheory.Rg.Sw.LC.CoreC.symK_tr
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:57:36.609983+00:00
-- url     : https://prove2.me/theorems/71b0ce46-e341-4a37-972d-ecdbd473c2c2
-- title:
--   Core C: sym K tr
-- statement:
--   The Core C construction uses the sym K tr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/CoeffSmulX.lean#L159-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/CoeffSmulX.lean#L159-L163

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

theorem PositivityTheory.Rg.Sw.LC.CoreC.symK_tr (ε : Fin m → Bool) (i j : Fin n) (v u) :
    (symK ε j i (X u : Sym m n)).coeff (Finsupp.single v 1) = star ((symK ε i j (X v : Sym m n)).coeff (Finsupp.single u 1)) := by sorry
