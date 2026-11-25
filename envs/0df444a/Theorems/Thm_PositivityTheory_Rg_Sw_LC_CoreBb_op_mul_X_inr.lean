-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreBb_op_mul_X_inr
-- name    : PositivityTheory.Rg.Sw.LC.CoreBb.op_mul_X_inr
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:24:17.258956+00:00
-- url     : https://prove2.me/theorems/362b3065-2351-4583-b7f2-ab1b803fff44
-- title:
--   Core Bb: op mul X inr
-- statement:
--   The Core Bb construction uses the op mul X inr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/ProdMapPowSingle.lean#L137-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/ProdMapPowSingle.lean#L137-L150

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

theorem PositivityTheory.Rg.Sw.LC.CoreBb.op_mul_X_inr (s : Sym m n) (k : Fin m × Fin n × Bool) (f : PX m n) :
    op (s * X (Sum.inr k)) f = op s (pderiv k f) := by sorry
