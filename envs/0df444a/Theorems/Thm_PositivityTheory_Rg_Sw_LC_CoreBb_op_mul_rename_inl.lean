-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreBb_op_mul_rename_inl
-- name    : PositivityTheory.Rg.Sw.LC.CoreBb.op_mul_rename_inl
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:59:53.946373+00:00
-- url     : https://prove2.me/theorems/d4326545-7ca3-4e53-be90-be822d63441b
-- title:
--   Core Bb: op mul rename inl
-- statement:
--   The Core Bb construction uses the op mul rename inl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/ProdMapPowSingle.lean#L152-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/ProdMapPowSingle.lean#L152-L157

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

theorem PositivityTheory.Rg.Sw.LC.CoreBb.op_mul_rename_inl (s : Sym m n) (g f : PX m n) :
    op (s * rename Sum.inl g) f = g * op s f := by sorry
