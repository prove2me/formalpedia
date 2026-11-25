-- Prove2me | Theorems.Thm_P2M_PositivityTheory_Rg_Sw_LC_NullS_sumT__9219b03eb577
-- name    : P2M_PositivityTheory_Rg_Sw_LC_NullS_sumT__9219b03eb577
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:10:38.271329+00:00
-- url     : https://prove2.me/theorems/ad376502-1f3f-41b9-93fd-c9575b56fc95
-- title:
--   P2 M Positivity Theory Rg Sw LC Null S sum T  9219b03eb577: P2 M Positivity Theory Rg Sw LC Null S sum T  9219b03eb577
-- statement:
--   The P2 M Positivity Theory Rg Sw LC Null S sum T  9219b03eb577 construction uses the P2 M Positivity Theory Rg Sw LC Null S sum T  9219b03eb577 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/SumPderivXMem.lean#L116-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/SumPderivXMem.lean#L116-L123

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PartialDerivQuadraticPairing
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_SumPderivXMem
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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.NullS
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
variable {m n : ℕ}

theorem P2M_PositivityTheory_Rg_Sw_LC_NullS_sumT__9219b03eb577 (ε : Fin m → Bool) (p q : Prop) [Decidable p] [Decidable q] (k l : Fin n) :
    (∑ a, C (sgn ε a) * ((if p then C (sgn ε a) * X (a, k, true) else 0) *
      (if q then C (sgn ε a) * X (a, l, false) else 0)) : PX m n) = if p ∧ q then Qp ε k l else 0 := by sorry

alias «PositivityTheory».«Rg».«Sw».«LC».«NullS».«sumT'» := P2M_PositivityTheory_Rg_Sw_LC_NullS_sumT__9219b03eb577
