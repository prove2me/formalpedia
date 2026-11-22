-- Prove2me | Theorems.Thm_ParallelPostulate_HyperbolicPlane_leaningFigure_angles
-- name    : ParallelPostulate.HyperbolicPlane.leaningFigure_angles
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:16:19.492167+00:00
-- url     : https://prove2.me/theorems/821c8909-d235-4e9b-9599-f44c9a082e57
-- title:
--   Hyperbolic Plane: leaning Figure angles
-- statement:
--   **The two interior angles of the figure, as far as numbers can show them.** At `a0`, which
--   is `(0, 0)`, the directions of `a` and `b` have the inner product 0. The motion along the first
--   axis with `a = -3/5` and `w = 4/5` takes `a1` to `(0, 0)`, `a0` to `(-3/5, 0)`, and `c1` to
--   `(-15/169, 100/169)`. So after the motion `c` leaves `(0, 0)`, and the inner product of its
--   direction with the direction of `a` run backwards is positive.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L3726-L3740
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L3726-L3740

module
public import Definitions.Def_LeanPool_ParallelPostulate_Geometry
public import Definitions.Def_LeanPool_ParallelPostulate_Hilbert
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.LineDeriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Arsinh
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Definitions.Def_LeanPool_ParallelPostulate
set_option autoImplicit true
@[expose] public section
public section
open ParallelPostulate
open ParallelPostulate.HyperbolicPlane
open Pairs

theorem ParallelPostulate.HyperbolicPlane.leaningFigure_angles :
    leaningFigure.a.dir.1 * leaningFigure.b.dir.1
        + leaningFigure.a.dir.2 * leaningFigure.b.dir.2 = 0 ∧
      ((4 / 5 : ℚ)) ^ 2 = 1 + (-1) * (-3 / 5) ^ 2 ∧
      shift (-1 : ℚ) (-3 / 5) (4 / 5) leaningFigure.a.one = (0, 0) ∧
      shift (-1 : ℚ) (-3 / 5) (4 / 5) leaningFigure.a.zero = (-3 / 5, 0) ∧
      shift (-1 : ℚ) (-3 / 5) (4 / 5) leaningFigure.c.one = (-15 / 169, 100 / 169) ∧
      (0 : ℚ) < (-15 / 169) * (-3 / 5) + (100 / 169) * 0 := by sorry
