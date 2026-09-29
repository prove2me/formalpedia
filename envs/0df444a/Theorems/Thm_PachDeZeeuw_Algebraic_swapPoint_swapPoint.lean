-- Prove2me | Theorems.Thm_PachDeZeeuw_Algebraic_swapPoint_swapPoint
-- name    : PachDeZeeuw.Algebraic.swapPoint_swapPoint
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-17T01:38:56.76308+00:00
-- url     : https://prove2.me/theorems/15772445-f885-4571-b9e1-8830c067837d
-- title:
--   $\mathrm{swapPoint}$ is an involution on the plane
-- statement:
--   Let $z : \mathrm{Point2}$ be any point of the Euclidean plane, and let $\mathrm{swapPoint}$ be the coordinate-swap map $z \mapsto \mathrm{mkPoint2}\,(z\,1)\,(z\,0)$. Then swapping twice is the identity:
--
--   $${\mathrm{swapPoint}\,(\mathrm{swapPoint}\,z) = z.}$$
--
--   This identity is used only inside the two nonsingular-point lemmas: the $\partial_0$ case (`nonsingular_point_has_infinite_zeroSet_of_partial0`) is derived from the $\partial_1$ case by renaming the two variables of the polynomial with the swap and moving points with $\mathrm{swapPoint}$. The identity shows that $\mathrm{swapPoint}$ is injective and that it maps the zero set of the renamed polynomial onto the zero set of the original one. The pair-intersection analysis does not swap coordinates.
-- source:
--   Lean bridge lemma (definitional unfolding or coordinate bookkeeping) for the formalization of Pach–de Zeeuw, arXiv:1308.0177, Theorem 2.1; not a literature statement; formalized in https://github.com/mysticflounder/lean-formalizations/blob/dd46c17a2a034d7bfa0df02e7f77834d35592864/lean/LeanFormalizations/PachDeZeeuw/Bezout.lean#L462-L465

import Mathlib
import Definitions.Def_PdzBezout
import Definitions.Def_PdzPrelim

open EuclideanGeometry
open scoped Topology
open PachDeZeeuw.Algebraic
open PachDeZeeuw.Algebraic.PlaneCurve

theorem PachDeZeeuw.Algebraic.swapPoint_swapPoint (z : Point2) : swapPoint (swapPoint z) = z := by sorry
