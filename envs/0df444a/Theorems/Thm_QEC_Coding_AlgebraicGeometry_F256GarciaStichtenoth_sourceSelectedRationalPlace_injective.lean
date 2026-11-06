-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceSelectedRationalPlace_injective
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSelectedRationalPlace_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:48:17.4136+00:00
-- url     : https://prove2.me/theorems/49b190f0-4fc0-48f8-8fd9-e649042f550e
-- title:
--   F256 Garcia Stichtenoth: source Selected Rational Place injective
-- statement:
--   Distinct finite source paths give distinct selected rational places.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceSelectedPlaces.lean#L268-L292
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceSelectedPlaces.lean#L268-L292

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceRecursion
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceSplitEvaluation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceSelectedPlaces
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSelectedRationalPlace_injective :
    ∀ i : ℕ, Function.Injective (sourceSelectedRationalPlace i)
  := by sorry
