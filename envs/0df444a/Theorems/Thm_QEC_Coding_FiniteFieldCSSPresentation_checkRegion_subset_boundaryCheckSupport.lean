-- Prove2me | Theorems.Thm_QEC_Coding_FiniteFieldCSSPresentation_checkRegion_subset_boundaryCheckSupport
-- name    : QEC.Coding.FiniteFieldCSSPresentation.checkRegion_subset_boundaryCheckSupport
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:08:50.254501+00:00
-- url     : https://prove2.me/theorems/4095e73a-3835-4b66-b8fd-6356d60387d4
-- title:
--   Finite Field CSSPresentation: check Region subset boundary Check Support
-- statement:
--   Every semantic check region is contained in the support of its base
--   boundary row. In particular scalar decoration never increases row weight.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FiniteFieldCSSPresentation.lean#L205-L214
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FiniteFieldCSSPresentation.lean#L205-L214

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

theorem QEC.Coding.FiniteFieldCSSPresentation.checkRegion_subset_boundaryCheckSupport
    (K : ChainComplexData F (Word F κ₀) (Word F ι) (Word F κ₂))
    (c : CheckIndex F κ₀ κ₂) :
    ((presentation K).checks c).region.selected ⊆
      (QLDPC.chainComplexBoundaryIncidence K).checkSupport
        (baseCheckIndex c) := by sorry
