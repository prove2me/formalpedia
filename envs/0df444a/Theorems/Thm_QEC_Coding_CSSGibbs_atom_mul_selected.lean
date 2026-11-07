-- Prove2me | Theorems.Thm_QEC_Coding_CSSGibbs_atom_mul_selected
-- name    : QEC.Coding.CSSGibbs.atom_mul_selected
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:29:57.280245+00:00
-- url     : https://prove2.me/theorems/5b2b1ea3-aa81-46f5-a213-1bc972893cd5
-- title:
--   CSSGibbs: atom mul selected
-- statement:
--   The CSSGibbs construction uses the atom mul selected property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/GibbsSyndrome/Selection.lean#L38-L56
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/GibbsSyndrome/Selection.lean#L38-L56

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

theorem QEC.Coding.CSSGibbs.atom_mul_selected (a : Realizable P Q) (A : Finset (Realizable P Q)) :
    projector P Q horth (realizableEmbedding P Q a) * selectedProjector P Q horth A =
      if a ∈ A then projector P Q horth (realizableEmbedding P Q a) else 0 := by sorry
