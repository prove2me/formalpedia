-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_mem_sourceStepArtinSchreierRoots
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.mem_sourceStepArtinSchreierRoots
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:55:58.952885+00:00
-- url     : https://prove2.me/theorems/a5918e0c-7edb-4417-b1b7-c25be15ea83f
-- title:
--   F256 Garcia Stichtenoth: mem source Step Artin Schreier Roots
-- statement:
--   The F256 Garcia Stichtenoth construction uses the mem source Step Artin Schreier Roots property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceSplitAlgebra.lean#L107-L111
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceSplitAlgebra.lean#L107-L111

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_GaloisBase
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisStep
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceSplitAlgebra
set_option autoImplicit false
open Polynomial
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.mem_sourceStepArtinSchreierRoots
    (a : GaloisBaseSplitPoint) (y : F256) :
    y ∈ sourceStepArtinSchreierRoots a ↔
      y ^ 16 + y = sourceStepRhs (a : F256) := by sorry
