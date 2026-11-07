-- Prove2me | Theorems.Thm_QEC_Coding_CSSGibbs_transport_add
-- name    : QEC.Coding.CSSGibbs.transport_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:32:16.827219+00:00
-- url     : https://prove2.me/theorems/8af8a2d1-9fe5-4006-bfb5-8034cba8647f
-- title:
--   CSSGibbs: transport add
-- statement:
--   Translation holds at every background, not just the all-plus sector.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/GibbsSyndrome/Translation.lean#L21-L34
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/GibbsSyndrome/Translation.lean#L21-L34

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

theorem QEC.Coding.CSSGibbs.transport_add (E : Binary ι) (s : Word (ZMod 2) (Sum κP κQ)) :
    transportSyndrome (binaryCSSParityCheckGenerators P Q) (checks_commute P Q horth)
      E (syndromeOutcome _ s) =
    syndromeOutcome _ (s + stabilizerSyndrome (binaryCSSParityCheckGenerators P Q) E) := by sorry
