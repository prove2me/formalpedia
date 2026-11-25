-- Prove2me | Theorems.Thm_P2M_GlobalTheory_FockRep_detPlus_eq_det_toBlocks___f9bcbd0bab63
-- name    : P2M_GlobalTheory_FockRep_detPlus_eq_det_toBlocks___f9bcbd0bab63
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T13:05:52.900978+00:00
-- url     : https://prove2.me/theorems/81b3b664-f063-50f4-a46e-d21c13cd54fb
-- title:
--   P2 M Global Theory Fock Rep det Plus eq det to Blocks   f9bcbd0bab63: P2 M Global Theory Fock Rep det Plus eq det to Blocks   f9bcbd0bab63
-- statement:
--   The P2 M Global Theory Fock Rep det Plus eq det to Blocks   f9bcbd0bab63 construction uses the P2 M Global Theory Fock Rep det Plus eq det to Blocks   f9bcbd0bab63 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsUnitaryOsc.lean#L31-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsUnitaryOsc.lean#L31-L43

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EqZeroOfOrthogonalTranslatesProj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsOscillatorActionOfGaussianPairings
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussianPairingUnitaryGroupTwoThree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsOscillatorActionUnitaryGroupHermitian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUnitaryOsc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.WeilM Matrix MeasureTheory Complex GlobalTheory.RealWeil GlobalTheory.RealWeil.UnitaryOsc
open scoped InnerProductSpace
open GlobalTheory GlobalTheory.FockRep

theorem P2M_GlobalTheory_FockRep_detPlus_eq_det_toBlocks___f9bcbd0bab63 {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] (g : Matrix (m ⊕ n) (m ⊕ n) ℂ) :
    dP (fromBlocks 1 0 0 (-1)) g = g.toBlocks₁₁.det := by sorry

alias «GlobalTheory».«FockRep».«detPlus_eq_det_toBlocks₁₁» := P2M_GlobalTheory_FockRep_detPlus_eq_det_toBlocks___f9bcbd0bab63
