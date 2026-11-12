-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PairedDecoderPhase_actual_Y_nonzero_overlap
-- name    : QEC.Coding.BDL26PairedDecoderPhase.actual_Y_nonzero_overlap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T18:27:53.372804+00:00
-- url     : https://prove2.me/theorems/8b2599c4-3ffe-4db1-916f-e7d8a73f2233
-- title:
--   BDL26 Paired Decoder Phase: actual Y nonzero overlap
-- statement:
--   Both Y coordinates are nonzero and overlap at the actual physical site.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/PairedDecoderPhase.lean#L402-L411
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/PairedDecoderPhase.lean#L402-L411

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TransposedStoppedDecoder
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_SectorTranslation
import Definitions.Def_QEC_Coding_Stabilizer_GoodSyndromeProtectedSector
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderPhase
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26PairedDecoderPhase
open Classical Semantics PauliSymplectic BDL26FiniteTannerSquare
open BDL26CSSHamiltonian BDL26TransposedStoppedDecoder
open StabilizerCode.DecoderDressedLogical
open scoped BigOperators
variable (S : OddScale) (n : Nat)
attribute [local instance] QEC.Coding.BDL26PairedDecoderPhase._p2m_local_instance_6635fd3be7_27
attribute [local instance] QEC.Coding.BDL26PairedDecoderPhase._p2m_local_instance_6635fd3be7_28

theorem QEC.Coding.BDL26PairedDecoderPhase.actual_Y_nonzero_overlap (q : Physical S (n + 2)) :
    (CSSDaviesLocality.singlePauli q .y).vector.xPart ≠ 0 ∧
    (CSSDaviesLocality.singlePauli q .y).vector.zPart ≠ 0 ∧
    (CSSDaviesLocality.singlePauli q .y).vector.xPart q *
      (CSSDaviesLocality.singlePauli q .y).vector.zPart q = 1 := by sorry
