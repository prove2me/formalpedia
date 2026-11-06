-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceSplitAbovePlace_order_sourceStepEmbedding
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSplitAbovePlace_order_sourceStepEmbedding
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:35:34.307+00:00
-- url     : https://prove2.me/theorems/075f6a75-03b3-43d2-a4d0-870fc3319571
-- title:
--   F256 Garcia Stichtenoth: source Split Above Place order source Step Embedding
-- statement:
--   At a selected source upper place, normalized order restricts unchanged to
--   every nonzero lower-field element.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceSplitOrder.lean#L153-L236
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceSplitOrder.lean#L153-L236

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceRationalSplitting
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceSplitOrder
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K] [Algebra F256 K]

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSplitAbovePlace_order_sourceStepEmbedding
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (hregular : GlobalPlace.RegularAt Q.place x)
    (hsplit : galoisBaseWValue (Q.evaluateRegular x hregular) ≠ 0)
    (c : LinearMap.ker f256ArtinSchreier)
    (y : K) (hy : y ≠ 0) :
    (sourceSplitAbovePlace Q P x hx c).order
        (sourceStepEmbedding P x hx y) = Q.place.order y := by sorry
