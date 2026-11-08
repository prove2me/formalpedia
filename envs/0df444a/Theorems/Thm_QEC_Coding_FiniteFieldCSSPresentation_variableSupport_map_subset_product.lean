-- Prove2me | Theorems.Thm_QEC_Coding_FiniteFieldCSSPresentation_variableSupport_map_subset_product
-- name    : QEC.Coding.FiniteFieldCSSPresentation.variableSupport_map_subset_product
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:08:58.325435+00:00
-- url     : https://prove2.me/theorems/45254c36-055f-4923-91a0-cafeae02ce3a
-- title:
--   Finite Field CSSPresentation: variable Support map subset product
-- statement:
--   The scalar-decorated semantic checks incident to a coordinate inject into
--   the product of its algebraic incident rows with all field scalars.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FiniteFieldCSSPresentation.lean#L218-L232
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FiniteFieldCSSPresentation.lean#L218-L232

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

theorem QEC.Coding.FiniteFieldCSSPresentation.variableSupport_map_subset_product
    (K : ChainComplexData F (Word F κ₀) (Word F ι) (Word F κ₂))
    (q : ι) :
    ((presentation K).incidence.variableSupport q).map
        checkIndexEquiv.toEmbedding ⊆
      (QLDPC.chainComplexBoundaryIncidence K).variableSupport q ×ˢ
        (Finset.univ : Finset F) := by sorry
