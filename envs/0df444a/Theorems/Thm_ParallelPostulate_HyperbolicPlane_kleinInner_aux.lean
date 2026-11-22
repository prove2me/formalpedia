-- Prove2me | Theorems.Thm_ParallelPostulate_HyperbolicPlane_kleinInner_aux
-- name    : ParallelPostulate.HyperbolicPlane.kleinInner_aux
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:13:19.697413+00:00
-- url     : https://prove2.me/theorems/51827803-b403-4b65-b5b8-45c162da1ee7
-- title:
--   Hyperbolic Plane: klein Inner aux
-- statement:
--   The algebra of the next theorem, with the divisions taken out.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L1533-L1578
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L1533-L1578

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

theorem ParallelPostulate.HyperbolicPlane.kleinInner_aux (κ a w xP yP xA yA xB yB XP YP XA YA XB YB : K)
    (hw : w ^ 2 = 1 + κ * a ^ 2)
    (hXP : XP * (1 - κ * a * xP) = xP + a) (hYP : YP * (1 - κ * a * xP) = w * yP)
    (hXA : XA * (1 - κ * a * xA) = xA + a) (hYA : YA * (1 - κ * a * xA) = w * yA)
    (hXB : XB * (1 - κ * a * xB) = xB + a) (hYB : YB * (1 - κ * a * xB) = w * yB) :
    ((XA - XP) * (XB - XP) + (YA - YP) * (YB - YP)
        + κ * (XP * YA - YP * XA) * (XP * YB - YP * XB))
        * ((1 - κ * a * xP) ^ 2 * (1 - κ * a * xA) * (1 - κ * a * xB))
      = w ^ 4 * ((xA - xP) * (xB - xP) + (yA - yP) * (yB - yP)
        + κ * (xP * yA - yP * xA) * (xP * yB - yP * xB)) := by sorry
