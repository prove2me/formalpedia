-- Prove2me | Theorems.Thm_UnitCircleRetainedArcEndpointQuotient
-- name    : UnitCircleRetainedArcEndpointQuotient
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T18:42:19.654123+00:00
-- url     : https://prove2.me/theorems/4b39f1bc-6589-4c95-a054-68536a1d8763
-- title:
--   Unit Circle Retained Arc Endpoint Quotient
-- statement:
--   Let $P\subset\mathbb{R}^2$ be finite, and put
--   $$
--     R=\{p\in P: |P\cap\operatorname{UnitCircle}(p)|\ge 3\}.
--   $$
--   There are a finite index type $\iota$, a finite set $A\subseteq\iota$, an
--   endpoint map $\epsilon:\iota\to\operatorname{Sym}^2(P)$, and, for every
--   index $i$, data
--   $$
--     c_i,x_i,y_i\in P,\qquad
--     C_i,I_i\subseteq\mathbb R^2,\qquad
--     \gamma_i:[0,1]\to\mathbb R^2,
--   $$
--   with the following properties.  First,
--   $$
--     |A|=\sum_{p\in R}|P\cap\operatorname{UnitCircle}(p)|,
--   $$
--   every endpoint pair $\epsilon(i)$, $i\in A$, is non-diagonal, and every
--   endpoint pair in $\epsilon(A)$ has at most two preimages in $A$.  Second,
--   for every $i\in A$, the center $c_i$ is retained, $\epsilon(i)=\{x_i,y_i\}$,
--   $x_i\ne y_i$, and $x_i,y_i\in P\cap\operatorname{UnitCircle}(c_i)$.  The
--   map $\gamma_i$ is continuous and injective, lies on
--   $\operatorname{UnitCircle}(c_i)$, starts at $x_i$, ends at $y_i$, and
--   $$
--     C_i=\gamma_i([0,1]),\qquad I_i=\gamma_i((0,1)),\qquad
--     C_i\subseteq\operatorname{UnitCircle}(c_i).
--   $$
--   No vertex of $P$ lies in any $I_i$.  If $i,j\in A$ have the same center
--   and $i\ne j$, then $I_i\cap I_j=\varnothing$.  If $i,j\in A$ have the
--   same center and $\epsilon(i)=\epsilon(j)$, then $i=j$.
--
--   **Formalization Note** This node is ported from the Trellis formalization of the crossing lemma and its consequences ([wpegden/crossing-consequences](https://github.com/wpegden/crossing-consequences), commit `8769d142`, W. Pegden, Apache-2.0); the statement is the Trellis node `UnitCircleRetainedArcEndpointQuotient`.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/UnitCircleRetainedArcEndpointQuotient.lean#L1-L411

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
open scoped BigOperators
open scoped Real
noncomputable section

lemma UnitCircleRetainedArcEndpointQuotient
    (P : Finset (EuclideanSpace ℝ (Fin 2))) :
    ∃ (ι : Type) (instF : Fintype ι) (instD : DecidableEq ι)
      (A : Finset ι) (endpoint : ι → Sym2 P)
      (center arcStart arcEnd : ι → P)
      (carrier arcInterior : ι → Set (EuclideanSpace ℝ (Fin 2)))
      (γ : ι → Set.Icc (0 : ℝ) 1 → EuclideanSpace ℝ (Fin 2)),
      (A.card : ℝ) =
          ∑ p ∈ P.filter
            (fun p => 3 ≤ (P.filter (fun q => q ∈ UnitCircle p)).card),
            ((P.filter (fun q => q ∈ UnitCircle p)).card : ℝ) ∧
        (∀ i ∈ A, ¬ (endpoint i).IsDiag) ∧
          (∀ e ∈ A.image endpoint,
            (A.filter (fun i => endpoint i = e)).card ≤ 2) ∧
            (∀ i ∈ A,
              3 ≤ (P.filter
                (fun q => q ∈ UnitCircle (center i : EuclideanSpace ℝ (Fin 2)))).card) ∧
              (∀ i ∈ A, endpoint i = Sym2.mk (arcStart i) (arcEnd i)) ∧
                (∀ i ∈ A,
                  (arcStart i : EuclideanSpace ℝ (Fin 2)) ≠
                    (arcEnd i : EuclideanSpace ℝ (Fin 2))) ∧
                  (∀ i ∈ A,
                    (arcStart i : EuclideanSpace ℝ (Fin 2)) ∈
                        UnitCircle (center i : EuclideanSpace ℝ (Fin 2)) ∧
                      (arcEnd i : EuclideanSpace ℝ (Fin 2)) ∈
                        UnitCircle (center i : EuclideanSpace ℝ (Fin 2))) ∧
                    (∀ i ∈ A,
                      Continuous (γ i) ∧
                        Function.Injective (γ i) ∧
                          (∀ t, γ i t ∈
                            UnitCircle (center i : EuclideanSpace ℝ (Fin 2))) ∧
                            γ i ⟨0, by simp⟩ =
                              (arcStart i : EuclideanSpace ℝ (Fin 2)) ∧
                              γ i ⟨1, by simp⟩ =
                                (arcEnd i : EuclideanSpace ℝ (Fin 2)) ∧
                                carrier i = Set.range (γ i) ∧
                                  arcInterior i =
                                    Set.range
                                      (fun t : {t : ℝ // 0 < t ∧ t < 1} =>
                                        γ i
                                          ⟨t.1, ⟨le_of_lt t.2.1,
                                            le_of_lt t.2.2⟩⟩)) ∧
                      (∀ i ∈ A, carrier i ⊆
                        UnitCircle (center i : EuclideanSpace ℝ (Fin 2))) ∧
                        (∀ i ∈ A, ∀ v : P,
                          (v : EuclideanSpace ℝ (Fin 2)) ∉ arcInterior i) ∧
                          (∀ i ∈ A, ∀ j ∈ A,
                            center i = center j → i ≠ j →
                              arcInterior i ∩ arcInterior j = ∅) ∧
                            (∀ i ∈ A, ∀ j ∈ A,
                              center i = center j → endpoint i = endpoint j →
                                i = j) := by sorry
