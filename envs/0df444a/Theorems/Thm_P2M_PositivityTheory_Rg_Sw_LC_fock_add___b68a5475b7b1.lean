-- Prove2me | Theorems.Thm_P2M_PositivityTheory_Rg_Sw_LC_fock_add___b68a5475b7b1
-- name    : P2M_PositivityTheory_Rg_Sw_LC_fock_add___b68a5475b7b1
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:09:51.825232+00:00
-- url     : https://prove2.me/theorems/3881041c-06e8-45d1-a4bf-ad4e4afe11c6
-- title:
--   P2 M Positivity Theory Rg Sw LC fock add   b68a5475b7b1: P2 M Positivity Theory Rg Sw LC fock add   b68a5475b7b1
-- statement:
--   The P2 M Positivity Theory Rg Sw LC fock add   b68a5475b7b1 construction uses the P2 M Positivity Theory Rg Sw LC fock add   b68a5475b7b1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/HopPderivComm.lean#L79-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/HopPderivComm.lean#L79-L80

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_NullStableAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_HopPderivComm
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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
open PositivityTheory.Rg.Sw
variable {m n : ℕ}
variable (hB : FockBasic)
include hB

theorem P2M_PositivityTheory_Rg_Sw_LC_fock_add___b68a5475b7b1 {c : ℝ} (hc : 0 < c) (p q : PX m n) : fock c (p + q) = fock c p + fock c q := by sorry

alias «PositivityTheory».«Rg».«Sw».«LC».«fock_add''» := P2M_PositivityTheory_Rg_Sw_LC_fock_add___b68a5475b7b1
