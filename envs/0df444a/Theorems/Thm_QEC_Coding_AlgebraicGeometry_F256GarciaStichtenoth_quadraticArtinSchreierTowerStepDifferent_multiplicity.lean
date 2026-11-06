-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_quadraticArtinSchreierTowerStepDifferent_multiplicity
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.quadraticArtinSchreierTowerStepDifferent_multiplicity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:00:23.06805+00:00
-- url     : https://prove2.me/theorems/cd056549-e4cd-4c6e-afd5-52ef39d2c93f
-- title:
--   F256 Garcia Stichtenoth: quadratic Artin Schreier Tower Step Different multiplicity
-- statement:
--   Every actual local successor has different exponent two.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/QuadraticTower.lean#L202-L218
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/QuadraticTower.lean#L202-L218

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticStepDifferent
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticTower
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
universe u
variable {K : Type u} [Field K] [Algebra F256 K]

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.quadraticArtinSchreierTowerStepDifferent_multiplicity
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) (i : ℕ) :
    multiplicity
        (quadraticArtinSchreierUpperIdeal
          (quadraticArtinSchreierTowerPlace P a ha i)
          (quadraticArtinSchreierTowerCoordinate P a ha i)
          (quadraticArtinSchreierTowerCoordinate_order P a ha i))
        (differentIdeal
          (quadraticArtinSchreierTowerPlace P a ha i).valuationRing
          (QuadraticArtinSchreierIntegralClosure
            (quadraticArtinSchreierTowerPlace P a ha i)
            (quadraticArtinSchreierTowerCoordinate P a ha i)
            (quadraticArtinSchreierTowerCoordinate_order P a ha i))) = 2 := by sorry
