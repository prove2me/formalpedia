-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreBb_op_mul_X_inl
-- name    : PositivityTheory.Rg.Sw.LC.CoreBb.op_mul_X_inl
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:24:01.003339+00:00
-- url     : https://prove2.me/theorems/bac38fb6-fcc9-49e7-9e6d-ffb877f01406
-- title:
--   Core Bb: op mul X inl
-- statement:
--   The Core Bb construction uses the op mul X inl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/ProdMapPowSingle.lean#L121-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/ProdMapPowSingle.lean#L121-L135

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

theorem PositivityTheory.Rg.Sw.LC.CoreBb.op_mul_X_inl (s : Sym m n) (k : Fin m × Fin n × Bool) (f : PX m n) :
    op (s * X (Sum.inl k)) f = X k * op s f := by sorry
