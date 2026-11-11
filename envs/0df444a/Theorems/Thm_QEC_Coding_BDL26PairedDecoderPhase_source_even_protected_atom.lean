-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PairedDecoderPhase_source_even_protected_atom
-- name    : QEC.Coding.BDL26PairedDecoderPhase.source_even_protected_atom
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T18:31:30.345791+00:00
-- url     : https://prove2.me/theorems/a7b5e6b9-55fd-4e90-97c0-74398ee8d9d5
-- title:
--   BDL26 Paired Decoder Phase: source even protected atom
-- statement:
--   One all-parity, literal C2-inclusive source-even consumer.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/PairedDecoderPhase.lean#L481-L489
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/PairedDecoderPhase.lean#L481-L489

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

theorem QEC.Coding.BDL26PairedDecoderPhase.source_even_protected_atom (k : Nat) (hk : 1 ≤ k) :
    ∃ j : Nat, j + 2 = 2 * k ∧
      ∀ (s : Visible S j) (E logical : Binary (Physical S (j + 2))),
      (code S j).InBinaryNormalizer logical →
      (∃ a, wordLinearMapTranspose (xSyndrome S (j + 2)) a = (residual S j s E).vector.xPart) →
      (∃ b, wordLinearMapTranspose (zSyndrome S (j + 2)) b = (residual S j s E).vector.zPart) →
      (toHermitianQubitOperator E * dressed S j logical - dressed S j logical * toHermitianQubitOperator E) *
        atom S j s = 0 := by sorry
