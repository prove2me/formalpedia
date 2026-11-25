-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_symK_hlin
-- name    : PositivityTheory.Rg.Sw.LC.CoreC.symK_hlin
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:56:56.311922+00:00
-- url     : https://prove2.me/theorems/de5bfaee-f37a-4b24-8d1a-324d61c7e574
-- title:
--   Core C: sym K hlin
-- statement:
--   The Core C construction uses the sym K hlin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/CoeffSmulX.lean#L154-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/CoeffSmulX.lean#L154-L157

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

theorem PositivityTheory.Rg.Sw.LC.CoreC.symK_hlin (ε : Fin m → Bool) (i j : Fin n) (v) :
    symK ε i j (X v : Sym m n) = ∑ u, (symK ε i j (X v : Sym m n)).coeff (Finsupp.single u 1) • X u := by sorry
