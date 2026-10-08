-- Prove2me | Theorems.Thm_UnitCircleCyclicSuccessorArcs
-- name    : UnitCircleCyclicSuccessorArcs
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T18:41:58.69537+00:00
-- url     : https://prove2.me/theorems/d581d449-39ce-4595-b92f-e5989d8587bf
-- title:
--   Unit Circle Cyclic Successor Arcs
-- statement:
--   Let $p\in\mathbb R^2$, and let $S$ be a finite set of points with
--   $$
--     S\subseteq \operatorname{UnitCircle}(p)
--     \qquad\text{and}\qquad
--     |S|\ge 3 .
--   $$
--   There are a successor map $\sigma:S\to S$, carrier sets $C_x\subseteq
--   \mathbb R^2$, relative-interior sets $I_x\subseteq\mathbb R^2$, and
--   parametrizations $\gamma_x:[0,1]\to\mathbb R^2$, indexed by $x\in S$, such
--   that:
--   $$
--     \sigma \text{ is bijective},\qquad x\ne\sigma(x)\quad\text{for every }x\in S;
--   $$
--   for every $x\in S$, the map $\gamma_x$ is continuous and injective, all
--   points of $\gamma_x([0,1])$ lie in $\operatorname{UnitCircle}(p)$,
--   $$
--     \gamma_x(0)=x,\qquad \gamma_x(1)=\sigma(x),\qquad
--     C_x=\gamma_x([0,1]),\qquad I_x=\gamma_x((0,1));
--   $$
--   no point of $S$ lies in any $I_x$; distinct indices have disjoint interiors,
--   $$
--     x\ne y\Longrightarrow I_x\cap I_y=\varnothing;
--   $$
--   and the unordered endpoint pair determines the index,
--   $$
--     \{x,\sigma(x)\}=\{y,\sigma(y)\}\Longrightarrow x=y .
--   $$
--
--   **Formalization Note** This node is ported from the Trellis formalization of the crossing lemma and its consequences ([wpegden/crossing-consequences](https://github.com/wpegden/crossing-consequences), commit `8769d142`, W. Pegden, Apache-2.0); the statement is the Trellis node `UnitCircleCyclicSuccessorArcs`.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/UnitCircleCyclicSuccessorArcs.lean#L1-L50

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Definitions.Def_UnitCircle

open Classical
noncomputable section

lemma UnitCircleCyclicSuccessorArcs
    (p : EuclideanSpace ℝ (Fin 2))
    (S : Finset (EuclideanSpace ℝ (Fin 2)))
    (hS : (↑S : Set (EuclideanSpace ℝ (Fin 2))) ⊆ UnitCircle p)
    (hcard : 3 ≤ S.card) :
    ∃ (succ :
        {x : EuclideanSpace ℝ (Fin 2) // x ∈ S} →
          {x : EuclideanSpace ℝ (Fin 2) // x ∈ S})
      (carrier arcInterior :
        {x : EuclideanSpace ℝ (Fin 2) // x ∈ S} →
          Set (EuclideanSpace ℝ (Fin 2)))
      (γ :
        (x : {x : EuclideanSpace ℝ (Fin 2) // x ∈ S}) →
          Set.Icc (0 : ℝ) 1 → EuclideanSpace ℝ (Fin 2)),
      Function.Bijective succ ∧
        (∀ x, x.1 ≠ (succ x).1) ∧
          (∀ x,
            Continuous (γ x) ∧
              Function.Injective (γ x) ∧
                (∀ t, γ x t ∈ UnitCircle p) ∧
                  γ x ⟨0, by simp⟩ = x.1 ∧
                    γ x ⟨1, by simp⟩ = (succ x).1 ∧
                      carrier x = Set.range (γ x) ∧
                        arcInterior x =
                          Set.range
                            (fun t : {t : ℝ // 0 < t ∧ t < 1} =>
                              γ x ⟨t.1, ⟨le_of_lt t.2.1, le_of_lt t.2.2⟩⟩)) ∧
            (∀ x y : {y : EuclideanSpace ℝ (Fin 2) // y ∈ S},
              y.1 ∉ arcInterior x) ∧
              (∀ x y,
                x ≠ y → arcInterior x ∩ arcInterior y = ∅) ∧
                (∀ x y,
                  (Sym2.mk x.1 (succ x).1 :
                      Sym2 (EuclideanSpace ℝ (Fin 2))) =
                    Sym2.mk y.1 (succ y).1 →
                    x = y) := by sorry
