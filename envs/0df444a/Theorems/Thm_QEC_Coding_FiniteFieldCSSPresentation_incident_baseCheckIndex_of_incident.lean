-- Prove2me | Theorems.Thm_QEC_Coding_FiniteFieldCSSPresentation_incident_baseCheckIndex_of_incident
-- name    : QEC.Coding.FiniteFieldCSSPresentation.incident_baseCheckIndex_of_incident
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:08:38.59232+00:00
-- url     : https://prove2.me/theorems/81963c03-4a8a-4dcc-80e7-3c6b40449c7d
-- title:
--   Finite Field CSSPresentation: incident base Check Index of incident
-- statement:
--   A semantic scalar check can only touch coordinates touched by its
--   underlying algebraic boundary row.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FiniteFieldCSSPresentation.lean#L176-L201
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FiniteFieldCSSPresentation.lean#L176-L201

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

theorem QEC.Coding.FiniteFieldCSSPresentation.incident_baseCheckIndex_of_incident
    (K : ChainComplexData F (Word F κ₀) (Word F ι) (Word F κ₂))
    (c : CheckIndex F κ₀ κ₂) (q : ι)
    (hq : (presentation K).incidence.incident c q) :
    (QLDPC.chainComplexBoundaryIncidence K).incident (baseCheckIndex c) q := by sorry
