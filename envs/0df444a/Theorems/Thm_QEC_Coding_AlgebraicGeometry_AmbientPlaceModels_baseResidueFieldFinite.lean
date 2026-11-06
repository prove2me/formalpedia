-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_AmbientPlaceModels_baseResidueFieldFinite
-- name    : QEC.Coding.AlgebraicGeometry.AmbientPlaceModels.baseResidueFieldFinite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:39:54.923282+00:00
-- url     : https://prove2.me/theorems/03215118-5c2b-4527-8dca-5d332d502136
-- title:
--   Ambient Place Models: base Residue Field Finite
-- statement:
--   The Ambient Place Models construction uses the base Residue Field Finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/AmbientPlaceModels.lean#L75-L77
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/AmbientPlaceModels.lean#L75-L77

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_RestrictedIntegralModel
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_DifferentialLocal
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_AmbientPlaceModels
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.AmbientPlaceModels
noncomputable section
variable {k E : Type*} [Field k] [Finite k] [Field E] [Algebra k E]
    (F : Type*) [Field F] [Algebra k F] [Algebra F E]
    [FiniteDimensional F E] [Algebra.IsSeparable F E]
    (Q : GlobalPlace k E)
omit [FiniteDimensional F E]

theorem QEC.Coding.AlgebraicGeometry.AmbientPlaceModels.baseResidueFieldFinite [Finite Q.residueField] :
    Finite (IsLocalRing.ResidueField (baseRing F Q)) := by sorry
