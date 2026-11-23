-- Prove2me | Theorems.Thm_P2M_PositivityTheory_Rg_Sw_LC_B3_op_sum__6a1d2ce1b97d
-- name    : P2M_PositivityTheory_Rg_Sw_LC_B3_op_sum__6a1d2ce1b97d
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T19:38:50.2888+00:00
-- url     : https://prove2.me/theorems/4796b64b-0295-440e-a65b-62f5ea9668e9
-- title:
--   P2 M Positivity Theory Rg Sw LC B3 op sum  6a1d2ce1b97d: P2 M Positivity Theory Rg Sw LC B3 op sum  6a1d2ce1b97d
-- statement:
--   The P2 M Positivity Theory Rg Sw LC B3 op sum  6a1d2ce1b97d construction uses the P2 M Positivity Theory Rg Sw LC B3 op sum  6a1d2ce1b97d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/SymmetricFiltrationIffSupported.lean#L199-L204
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/SymmetricFiltrationIffSupported.lean#L199-L204

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

theorem P2M_PositivityTheory_Rg_Sw_LC_B3_op_sum__6a1d2ce1b97d {ι : Type*} (T : Finset ι) (u : ι → Sym m n) (f : PX m n) :
    op (∑ i ∈ T, u i) f = ∑ i ∈ T, op (u i) f := by sorry

alias «PositivityTheory».«Rg».«Sw».«LC».«B3».«op_sum'» := P2M_PositivityTheory_Rg_Sw_LC_B3_op_sum__6a1d2ce1b97d
