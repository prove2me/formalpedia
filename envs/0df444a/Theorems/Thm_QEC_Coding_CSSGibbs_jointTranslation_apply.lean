-- Prove2me | Theorems.Thm_QEC_Coding_CSSGibbs_jointTranslation_apply
-- name    : QEC.Coding.CSSGibbs.jointTranslation_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:31:51.498138+00:00
-- url     : https://prove2.me/theorems/6b3c3272-ba1b-4ef9-acba-be8bfbe45f64
-- title:
--   CSSGibbs: joint Translation apply
-- statement:
--   The CSSGibbs construction uses the joint Translation apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/GibbsSyndrome/Translation.lean#L71-L73
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/GibbsSyndrome/Translation.lean#L71-L73

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

theorem QEC.Coding.CSSGibbs.jointTranslation_apply (E : Binary ι) (s : Realizable P Q) :
    jointTranslation P Q E s =
      (rangeShift P E.vector.xPart s.1, rangeShift Q E.vector.zPart s.2) := by sorry

attribute [defeq] QEC.Coding.CSSGibbs.jointTranslation_apply
