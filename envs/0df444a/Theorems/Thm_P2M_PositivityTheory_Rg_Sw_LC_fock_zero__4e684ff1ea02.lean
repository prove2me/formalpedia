-- Prove2me | Theorems.Thm_P2M_PositivityTheory_Rg_Sw_LC_fock_zero__4e684ff1ea02
-- name    : P2M_PositivityTheory_Rg_Sw_LC_fock_zero__4e684ff1ea02
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:10:18.629774+00:00
-- url     : https://prove2.me/theorems/0c254c0d-9058-5d5b-8dd3-69c81f70a9aa
-- title:
--   P2 M Positivity Theory Rg Sw LC fock zero  4e684ff1ea02: P2 M Positivity Theory Rg Sw LC fock zero  4e684ff1ea02
-- statement:
--   The P2 M Positivity Theory Rg Sw LC fock zero  4e684ff1ea02 construction uses the P2 M Positivity Theory Rg Sw LC fock zero  4e684ff1ea02 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/HopPderivComm.lean#L82-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/HopPderivComm.lean#L82-L83

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

theorem P2M_PositivityTheory_Rg_Sw_LC_fock_zero__4e684ff1ea02 {c : ℝ} (hc : 0 < c) : fock c (0 : PX m n) = 0 := by sorry

alias «PositivityTheory».«Rg».«Sw».«LC».«fock_zero'» := P2M_PositivityTheory_Rg_Sw_LC_fock_zero__4e684ff1ea02
