-- Prove2me | Theorems.Thm_QEC_Coding_CSSGibbs_projector_commute
-- name    : QEC.Coding.CSSGibbs.projector_commute
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:30:31.490514+00:00
-- url     : https://prove2.me/theorems/e1652fc6-a1d3-49fa-98b8-9bcbdc447092
-- title:
--   CSSGibbs: projector commute
-- statement:
--   The CSSGibbs construction uses the projector commute property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/GibbsSyndrome/Selection.lean#L30-L36
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/GibbsSyndrome/Selection.lean#L30-L36

import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Gibbs
import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Selection
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.CSSGibbs
open Classical Semantics
open scoped BigOperators
variable {ι κP κQ : Type} [Fintype ι] [DecidableEq ι]
  [Fintype κP] [Fintype κQ] [DecidableEq κP] [DecidableEq κQ]
variable (P : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κP)
  (Q : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κQ)
  (horth : ∀ p q, wordPairing (parityCheckRow P p) (parityCheckRow Q q) = 0)
attribute [local instance] QEC.Coding.CSSGibbs._p2m_local_instance_807a85e857_19
attribute [local instance] QEC.Coding.CSSGibbs._p2m_local_instance_807a85e857_20

theorem QEC.Coding.CSSGibbs.projector_commute (s t : Word (ZMod 2) (Sum κP κQ)) :
    Commute (projector P Q horth s) (projector P Q horth t) := by sorry
