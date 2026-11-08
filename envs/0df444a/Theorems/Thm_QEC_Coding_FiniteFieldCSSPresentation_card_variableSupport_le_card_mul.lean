-- Prove2me | Theorems.Thm_QEC_Coding_FiniteFieldCSSPresentation_card_variableSupport_le_card_mul
-- name    : QEC.Coding.FiniteFieldCSSPresentation.card_variableSupport_le_card_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:08:50.040427+00:00
-- url     : https://prove2.me/theorems/561466b5-3d7c-4c64-bcfd-d93286b7c337
-- title:
--   Finite Field CSSPresentation: card variable Support le card mul
-- statement:
--   Decorating all base rows by finite-field scalars multiplies variable
--   degree by at most `|F|`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FiniteFieldCSSPresentation.lean#L236-L250
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FiniteFieldCSSPresentation.lean#L236-L250

import Definitions.Def_QEC_Coding_Stabilizer_FiniteFieldPauli
import Definitions.Def_QEC_Coding_Stabilizer_FiniteFieldCSSPresentation
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.FiniteFieldCSSPresentation
open QEC.Coding.FiniteFieldPauli
universe u
variable {F ι κ₀ κ₂ : Type u}
variable [Field F] [Fintype F]
variable [Fintype ι] [Fintype κ₀] [Fintype κ₂]
attribute [local instance] QEC.Coding.FiniteFieldCSSPresentation._p2m_local_instance_10414ac4d3_24

theorem QEC.Coding.FiniteFieldCSSPresentation.card_variableSupport_le_card_mul
    (K : ChainComplexData F (Word F κ₀) (Word F ι) (Word F κ₂))
    (q : ι) :
    ((presentation K).incidence.variableSupport q).card ≤
      ((QLDPC.chainComplexBoundaryIncidence K).variableSupport q).card *
        Fintype.card F := by sorry
