-- Prove2me | Theorems.Thm_SquarePeg_tao_two_lipschitz_graphs
-- name    : SquarePeg.tao_two_lipschitz_graphs
-- status  : Open
-- author  : @LG
-- created : 2026-11-21T23:22:56.975098+00:00
-- url     : https://prove2.me/theorems/fa6ec188-5f98-4f29-91ea-adf0e6f57822
-- title:
--   Tao's two-Lipschitz-graph inscribed square theorem
-- statement:
--   Let $f,g:[t_0,t_1]\to\mathbb{R}$ be Lipschitz functions with Lipschitz constant strictly less than $1$, agreeing at the endpoints, and suppose the union of their graphs is a Jordan curve $C$. Then $C$ inscribes a non-degenerate square. This is Tao's positive case of the square peg problem for a class of curves that need not be smooth.
-- source:
--   Tao, An integration approach to the Toeplitz square peg problem, Forum Math. Sigma 5 (2017), e30 (arXiv:1611.07441), the case of a union of two Lipschitz graphs of constant < 1 agreeing at the endpoints (blog announcement, Theorem 3(i)).

import Mathlib
import Definitions.Def_SchoenfliesCurveCore
import Definitions.Def_SquarePeg_shapes
import Definitions.Def_SquarePeg_classes
import Definitions.Def_SquarePeg_similarity
open Schoenflies

namespace SquarePeg

theorem tao_two_lipschitz_graphs (t0 t1 : ℝ) (ht : t0 < t1) (f g : ℝ → ℝ)
    (hf : ∃ K : NNReal, (K : ℝ) < 1 ∧ LipschitzOnWith K f (Set.Icc t0 t1))
    (hg : ∃ K : NNReal, (K : ℝ) < 1 ∧ LipschitzOnWith K g (Set.Icc t0 t1))
    (hends : f t0 = g t0 ∧ f t1 = g t1)
    (C : Set Plane)
    (hCdef : C = {p : Plane | p 0 ∈ Set.Icc t0 t1 ∧ (p 1 = f (p 0) ∨ p 1 = g (p 0))})
    (hC : IsJordanCurve C) :
    ∃ p1 p2 p3 p4 : Plane, p1 ∈ C ∧ p2 ∈ C ∧ p3 ∈ C ∧ p4 ∈ C ∧ IsSquare p1 p2 p3 p4 := by sorry

end SquarePeg
