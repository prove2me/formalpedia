-- Prove2me | Theorems.Thm_QEC_Coding_CSSGibbs_pauli_mul_realizable_projector
-- name    : QEC.Coding.CSSGibbs.pauli_mul_realizable_projector
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:32:11.988012+00:00
-- url     : https://prove2.me/theorems/8fe0d944-4026-4472-b7a4-d885c7f301e7
-- title:
--   CSSGibbs: pauli mul realizable projector
-- statement:
--   Atom transport uses the Hermitian physical Pauli, including its phase.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/GibbsSyndrome/Translation.lean#L91-L96
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/GibbsSyndrome/Translation.lean#L91-L96

import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Selection
import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Translation
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.CSSGibbs
open Classical PauliSymplectic StabilizerCode Semantics
open scoped BigOperators
variable {ι κP κQ : Type} [Fintype ι] [DecidableEq ι]
  [Fintype κP] [Fintype κQ] [DecidableEq κP] [DecidableEq κQ]
variable (P : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κP)
  (Q : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κQ)
  (horth : ∀ p q, wordPairing (parityCheckRow P p) (parityCheckRow Q q) = 0)
attribute [local instance] QEC.Coding.CSSGibbs._p2m_local_instance_22196e9987_17
attribute [local instance] QEC.Coding.CSSGibbs._p2m_local_instance_22196e9987_18

theorem QEC.Coding.CSSGibbs.pauli_mul_realizable_projector (E : Binary ι) (s : Realizable P Q) :
    toHermitianQubitOperator E * projector P Q horth (realizableEmbedding P Q s) =
      projector P Q horth (realizableEmbedding P Q (jointTranslation P Q E s)) *
        toHermitianQubitOperator E := by sorry
