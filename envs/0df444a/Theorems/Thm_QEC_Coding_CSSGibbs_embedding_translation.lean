-- Prove2me | Theorems.Thm_QEC_Coding_CSSGibbs_embedding_translation
-- name    : QEC.Coding.CSSGibbs.embedding_translation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:31:52.901012+00:00
-- url     : https://prove2.me/theorems/33cd1043-798b-499d-b4c1-8cc8237cfa4c
-- title:
--   CSSGibbs: embedding translation
-- statement:
--   The CSSGibbs construction uses the embedding translation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/GibbsSyndrome/Translation.lean#L83-L88
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/GibbsSyndrome/Translation.lean#L83-L88

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
include horth

theorem QEC.Coding.CSSGibbs.embedding_translation (E : Binary ι) (s : Realizable P Q) :
    realizableEmbedding P Q (jointTranslation P Q E s) =
      realizableEmbedding P Q s + stabilizerSyndrome (binaryCSSParityCheckGenerators P Q) E := by sorry
