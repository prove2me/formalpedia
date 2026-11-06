-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceStepArtinSchreierRoots_card
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceStepArtinSchreierRoots_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:55:39.477568+00:00
-- url     : https://prove2.me/theorems/cb44e7f8-4f5a-4ec9-b90a-3731c50d7b7c
-- title:
--   F256 Garcia Stichtenoth: source Step Artin Schreier Roots card
-- statement:
--   Every selected source-step Artin--Schreier fibre has exactly sixteen
--   constant roots.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceSplitAlgebra.lean#L138-L146
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceSplitAlgebra.lean#L138-L146

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_GaloisBase
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisStep
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceSplitAlgebra
set_option autoImplicit false
open Polynomial
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceStepArtinSchreierRoots_card (a : GaloisBaseSplitPoint) :
    (sourceStepArtinSchreierRoots a).card = 16 := by sorry
