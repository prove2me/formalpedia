-- Prove2me | Theorems.Thm_UnitCircleFundamentalAngles
-- name    : UnitCircleFundamentalAngles
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T18:42:06.592407+00:00
-- url     : https://prove2.me/theorems/f4cc8b31-96d4-4ac2-8c5d-da0543361a4a
-- title:
--   Unit Circle Fundamental Angles
-- statement:
--   Let $p\in\mathbb R^2$, and let $S$ be a finite set such that
--   $S\subseteq \operatorname{UnitCircle}(p)$.  Then there is a function
--   $$
--     \theta:S\to[0,2\pi)
--   $$
--   such that every $x\in S$ satisfies
--   $$
--     x=p+(\cos\theta(x),\sin\theta(x)),
--   $$
--   and this function $\theta$ is injective.
--
--   **Formalization Note** This node is ported from the Trellis formalization of the crossing lemma and its consequences ([wpegden/crossing-consequences](https://github.com/wpegden/crossing-consequences), commit `8769d142`, W. Pegden, Apache-2.0); the statement is the Trellis node `UnitCircleFundamentalAngles`.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/UnitCircleFundamentalAngles.lean#L1-L101

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Definitions.Def_UnitCircle

open Classical
noncomputable section

lemma UnitCircleFundamentalAngles
    (p : EuclideanSpace ℝ (Fin 2))
    (S : Finset (EuclideanSpace ℝ (Fin 2)))
    (hS : (↑S : Set (EuclideanSpace ℝ (Fin 2))) ⊆ UnitCircle p) :
    ∃ θ : {x : EuclideanSpace ℝ (Fin 2) // x ∈ S} → ℝ,
      (∀ x, 0 ≤ θ x ∧ θ x < 2 * Real.pi) ∧
      (∀ x,
        x.1 =
          p + WithLp.toLp 2
            (fun i : Fin 2 =>
              if i = 0 then Real.cos (θ x) else Real.sin (θ x))) ∧
      Function.Injective θ := by sorry
