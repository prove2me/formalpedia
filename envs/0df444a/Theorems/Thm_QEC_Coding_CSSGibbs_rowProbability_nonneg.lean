-- Prove2me | Theorems.Thm_QEC_Coding_CSSGibbs_rowProbability_nonneg
-- name    : QEC.Coding.CSSGibbs.rowProbability_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:29:55.593469+00:00
-- url     : https://prove2.me/theorems/6c16e966-e098-411f-94be-8033e99468ca
-- title:
--   CSSGibbs: row Probability nonneg
-- statement:
--   The CSSGibbs construction uses the row Probability nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/GibbsSyndrome/Selection.lean#L134-L136
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/GibbsSyndrome/Selection.lean#L134-L136

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

theorem QEC.Coding.CSSGibbs.rowProbability_nonneg (t : ℝ) (u : LinearMap.range P) :
    0 ≤ rowProbability P t u := by sorry
