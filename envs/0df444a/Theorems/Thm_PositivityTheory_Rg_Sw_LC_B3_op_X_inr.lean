-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_B3_op_X_inr
-- name    : PositivityTheory.Rg.Sw.LC.B3.op_X_inr
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:54:50.929883+00:00
-- url     : https://prove2.me/theorems/4ecc7c7f-6b88-49d4-ab8b-32c13cb1b699
-- title:
--   B3: op X inr
-- statement:
--   The B3 construction uses the op X inr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/SymmetricFiltrationIffSupported.lean#L195-L197
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/SymmetricFiltrationIffSupported.lean#L195-L197

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_ProdMapPowSingle
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PairSym
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PderivPowMonomial
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_SymmetricFiltrationIffSupported
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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.B3
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.CoreBb
variable {m n : ℕ}

theorem PositivityTheory.Rg.Sw.LC.B3.op_X_inr (k : Fin m × Fin n × Bool) (f : PX m n) : op (X (Sum.inr k) : Sym m n) f = pderiv k f := by sorry
