-- Prove2me | Theorems.Thm_QEC_Coding_CSSGibbs_pauli_conjugate_selected
-- name    : QEC.Coding.CSSGibbs.pauli_conjugate_selected
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:46:21.396611+00:00
-- url     : https://prove2.me/theorems/5d6b46b7-3754-40b9-97ed-63f330d2611d
-- title:
--   CSSGibbs: pauli conjugate selected
-- statement:
--   The CSSGibbs construction uses the pauli conjugate selected property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/GibbsSyndrome/Translation.lean#L117-L121
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/GibbsSyndrome/Translation.lean#L117-L121

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

theorem QEC.Coding.CSSGibbs.pauli_conjugate_selected (E : Binary ι) (A : Finset (Realizable P Q)) :
    toHermitianQubitOperator E * selectedProjector P Q horth A *
        toHermitianQubitOperator E =
      selectedProjector P Q horth (translatedSelection P Q E A) := by sorry
