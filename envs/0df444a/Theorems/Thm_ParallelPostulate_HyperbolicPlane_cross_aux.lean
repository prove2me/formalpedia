-- Prove2me | Theorems.Thm_ParallelPostulate_HyperbolicPlane_cross_aux
-- name    : ParallelPostulate.HyperbolicPlane.cross_aux
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:13:13.388281+00:00
-- url     : https://prove2.me/theorems/6ea9d01a-583d-4c50-98ce-f4f6d1f8f9a5
-- title:
--   Hyperbolic Plane: cross aux
-- statement:
--   The algebra of the next theorem, with the divisions taken out.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L1044-L1060
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L1044-L1060

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
variable {K : Type*} [Field K]

theorem ParallelPostulate.HyperbolicPlane.cross_aux (κ a w xA yA xB yB xC yC XA YA XB YB XC YC : K)
    (hXA : XA * (1 - κ * a * xA) = xA + a) (hYA : YA * (1 - κ * a * xA) = w * yA)
    (hXB : XB * (1 - κ * a * xB) = xB + a) (hYB : YB * (1 - κ * a * xB) = w * yB)
    (hXC : XC * (1 - κ * a * xC) = xC + a) (hYC : YC * (1 - κ * a * xC) = w * yC) :
    ((XB - XA) * (YC - YA) - (YB - YA) * (XC - XA))
        * ((1 - κ * a * xA) * (1 - κ * a * xB) * (1 - κ * a * xC))
      = w * (1 + κ * a ^ 2) * ((xB - xA) * (yC - yA) - (yB - yA) * (xC - xA)) := by sorry
