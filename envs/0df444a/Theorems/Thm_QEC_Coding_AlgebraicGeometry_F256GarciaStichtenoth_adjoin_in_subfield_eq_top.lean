-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_adjoin_in_subfield_eq_top
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.adjoin_in_subfield_eq_top
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:10:06.57614+00:00
-- url     : https://prove2.me/theorems/5db9004c-80b1-4071-8b7c-765c9835e4dd
-- title:
--   F256 Garcia Stichtenoth: adjoin in subfield eq top
-- statement:
--   The F256 Garcia Stichtenoth construction uses the adjoin in subfield eq top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/NormalizedCompositumEdges.lean#L23-L36
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/NormalizedCompositumEdges.lean#L23-L36

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_IntermediateIntegralModels
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticCompositumCell
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differents_RelativeTower
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_NormalizedCompositumEdges
set_option autoImplicit false
open IntermediateField
open scoped QEC.Coding.AlgebraicGeometry.IntermediateIntegralModels
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.adjoin_in_subfield_eq_top
    {F E : Type*} [_root_.Field F] [_root_.Field E] [Algebra F E]
    (K L : IntermediateField F E) [Fact (K ≤ L)]
    (z : E) (hz : z ∈ L) (hL : (K⟮z⟯).restrictScalars F = L) :
    K⟮(⟨z, hz⟩ : L)⟯ = ⊤ := by sorry
