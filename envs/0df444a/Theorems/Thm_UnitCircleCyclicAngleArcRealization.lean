-- Prove2me | Theorems.Thm_UnitCircleCyclicAngleArcRealization
-- name    : UnitCircleCyclicAngleArcRealization
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T18:41:50.969996+00:00
-- url     : https://prove2.me/theorems/cec808fc-17f4-49d5-adbc-13da8a04e14c
-- title:
--   Unit Circle Cyclic Angle Arc Realization
-- statement:
--   Let $p\in\mathbb R^2$, let $S\subset\mathbb R^2$ be finite, and suppose
--   that $D$ is $\operatorname{UnitCircleCyclicAngleData}(p,S)$ with successor
--   $\sigma$, starting angles $\theta_x$, and lifted terminal angles
--   $\Theta_x$.  Then there are carrier sets $C_x$, relative-interior sets
--   $I_x$, and parametrizations $\gamma_x:[0,1]\to\mathbb R^2$, indexed by
--   $x\in S$, such that for every $x\in S$, $\gamma_x$ is continuous and
--   injective, lies on $\operatorname{UnitCircle}(p)$, starts at $x$, ends at
--   $\sigma(x)$, and
--   $$
--     C_x=\gamma_x([0,1]),\qquad I_x=\gamma_x((0,1)).
--   $$
--   Moreover no point of $S$ lies in any $I_x$, and distinct indices have
--   disjoint relative interiors.
--
--   **Formalization Note** This node is ported from the Trellis formalization of the crossing lemma and its consequences ([wpegden/crossing-consequences](https://github.com/wpegden/crossing-consequences), commit `8769d142`, W. Pegden, Apache-2.0); the statement is the Trellis node `UnitCircleCyclicAngleArcRealization`.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/UnitCircleCyclicAngleArcRealization.lean#L1-L160

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Definitions.Def_UnitCircle
import Definitions.Def_UnitCircleCyclicAngleData

open Classical
noncomputable section

lemma UnitCircleCyclicAngleArcRealization
    (p : EuclideanSpace ℝ (Fin 2))
    (S : Finset (EuclideanSpace ℝ (Fin 2)))
    (D : UnitCircleCyclicAngleData p S) :
    ∃ (carrier arcInterior :
        {x : EuclideanSpace ℝ (Fin 2) // x ∈ S} →
          Set (EuclideanSpace ℝ (Fin 2)))
      (γ :
        (x : {x : EuclideanSpace ℝ (Fin 2) // x ∈ S}) →
          Set.Icc (0 : ℝ) 1 → EuclideanSpace ℝ (Fin 2)),
      (∀ x,
        Continuous (γ x) ∧
          Function.Injective (γ x) ∧
            (∀ t, γ x t ∈ UnitCircle p) ∧
              γ x ⟨0, by simp⟩ = x.1 ∧
                γ x ⟨1, by simp⟩ = (D.succ x).1 ∧
                  carrier x = Set.range (γ x) ∧
                    arcInterior x =
                      Set.range
                        (fun t : {t : ℝ // 0 < t ∧ t < 1} =>
                          γ x ⟨t.1, ⟨le_of_lt t.2.1, le_of_lt t.2.2⟩⟩)) ∧
        (∀ x y : {y : EuclideanSpace ℝ (Fin 2) // y ∈ S},
          y.1 ∉ arcInterior x) ∧
          (∀ x y,
            x ≠ y → arcInterior x ∩ arcInterior y = ∅) := by sorry
