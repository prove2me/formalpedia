-- Prove2me | Theorems.Thm_QEC_Coding_CSSGibbs_translatedSelection_product
-- name    : QEC.Coding.CSSGibbs.translatedSelection_product
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:46:22.749374+00:00
-- url     : https://prove2.me/theorems/8760e5b3-d7dd-4621-88ae-69cd6dbf2252
-- title:
--   CSSGibbs: translated Selection product
-- statement:
--   Rectangular selections translate componentwise, with no nonempty hypothesis.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/GibbsSyndrome/Translation.lean#L124-L138
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/GibbsSyndrome/Translation.lean#L124-L138

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

theorem QEC.Coding.CSSGibbs.translatedSelection_product (E : Binary ι)
    (A : Finset (LinearMap.range P)) (B : Finset (LinearMap.range Q)) :
    translatedSelection P Q E (A ×ˢ B) =
      (A.map (rangeShiftEquiv P E.vector.xPart).toEmbedding) ×ˢ
      (B.map (rangeShiftEquiv Q E.vector.zPart).toEmbedding) := by sorry
