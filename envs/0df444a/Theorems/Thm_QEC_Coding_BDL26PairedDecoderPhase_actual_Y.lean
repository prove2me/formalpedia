-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PairedDecoderPhase_actual_Y
-- name    : QEC.Coding.BDL26PairedDecoderPhase.actual_Y
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T17:56:51.451506+00:00
-- url     : https://prove2.me/theorems/81b4241d-9daf-46f2-9cde-81f06d1b5506
-- title:
--   BDL26 Paired Decoder Phase: actual Y
-- statement:
--   Y translates both sectors, and the operator retains its exact central i.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/PairedDecoderPhase.lean#L371-L376
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/PairedDecoderPhase.lean#L371-L376

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

theorem QEC.Coding.BDL26PairedDecoderPhase.actual_Y (s : Visible S n) (q : Physical S (n + 2)) :
    translation S n (CSSDaviesLocality.singlePauli q .y) s =
      (translateX S n s.1 (Pi.single q 1), translateZ S n s.2 (Pi.single q 1)) ∧
    BDL26CSSDaviesLocality.coupling S (n + 2) q .y =
      Complex.I • (Qubit.localX q * Qubit.localZ q) := by sorry
