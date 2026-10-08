-- Prove2me | Theorems.Thm_UnitCircleRetainedArcDrawingAssembly
-- name    : UnitCircleRetainedArcDrawingAssembly
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T18:42:21.392231+00:00
-- url     : https://prove2.me/theorems/4349ff78-10ae-4b93-b79a-0fb551ebc688
-- title:
--   Unit Circle Retained Arc Drawing Assembly
-- statement:
--   Let $P\subset\mathbb R^2$ be finite.  Let $A$ be a finite set of arc
--   indices, let $\epsilon:A\to\operatorname{Sym}^2(P)$ be an endpoint map, and
--   suppose that each index $i\in A$ is equipped with a center
--   $c_i\in P$, endpoint vertices $x_i,y_i\in P$, a carrier $C_i$, a
--   relative interior $I_i$, and a parametrization
--   $\gamma_i:[0,1]\to\mathbb R^2$.  Assume that
--   $$
--     \epsilon(i)=\{x_i,y_i\},\qquad x_i\ne y_i,
--   $$
--   that $x_i$ and $y_i$ lie on $\operatorname{UnitCircle}(c_i)$, and that
--   $\gamma_i$ is a continuous injective parametrization lying on
--   $\operatorname{UnitCircle}(c_i)$, starting at $x_i$, ending at $y_i$, with
--   $$
--     C_i=\gamma_i([0,1]),\qquad I_i=\gamma_i((0,1)),\qquad
--     C_i\subseteq\operatorname{UnitCircle}(c_i).
--   $$
--   Assume also that no vertex of $P$ lies in any $I_i$, and that whenever
--   two distinct indices of $A$ have the same center their relative interiors
--   are disjoint.
--
--   Then, for every finite simple graph $G$ on vertex set $P$ whose edge set is
--   exactly $\epsilon(A)$, there is a finite geometric-arc drawing $D$ of $G$
--   in the sense of `GeometricArcDrawing` such that
--   $$
--     D.\operatorname{localPairCount}\le 2|P|^2 .
--   $$
--
--   **Formalization Note** This node is ported from the Trellis formalization of the crossing lemma and its consequences ([wpegden/crossing-consequences](https://github.com/wpegden/crossing-consequences), commit `8769d142`, W. Pegden, Apache-2.0); the statement is the Trellis node `UnitCircleRetainedArcDrawingAssembly`.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/UnitCircleRetainedArcDrawingAssembly.lean#L1-L579

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Definitions.Def_GeometricArcDrawing
import Definitions.Def_UnitCircle

open Classical
open scoped BigOperators
open scoped Real
noncomputable section

lemma UnitCircleRetainedArcDrawingAssembly
    (P : Finset (EuclideanSpace ℝ (Fin 2)))
    {ι : Type} (A : Finset ι) (endpoint : ι → Sym2 P)
    (center arcStart arcEnd : ι → P)
    (carrier arcInterior : ι → Set (EuclideanSpace ℝ (Fin 2)))
    (γ : ι → Set.Icc (0 : ℝ) 1 → EuclideanSpace ℝ (Fin 2))
    (h_endpoint_eq : ∀ i ∈ A, endpoint i = Sym2.mk (arcStart i) (arcEnd i))
    (h_endpoints_distinct : ∀ i ∈ A,
      (arcStart i : EuclideanSpace ℝ (Fin 2)) ≠
        (arcEnd i : EuclideanSpace ℝ (Fin 2)))
    (h_endpoints_on_circle : ∀ i ∈ A,
      (arcStart i : EuclideanSpace ℝ (Fin 2)) ∈
          UnitCircle (center i : EuclideanSpace ℝ (Fin 2)) ∧
        (arcEnd i : EuclideanSpace ℝ (Fin 2)) ∈
          UnitCircle (center i : EuclideanSpace ℝ (Fin 2)))
    (h_arc_param : ∀ i ∈ A,
      Continuous (γ i) ∧
        Function.Injective (γ i) ∧
          (∀ t, γ i t ∈ UnitCircle (center i : EuclideanSpace ℝ (Fin 2))) ∧
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
                            le_of_lt t.2.2⟩⟩))
    (h_carrier_circle : ∀ i ∈ A, carrier i ⊆
      UnitCircle (center i : EuclideanSpace ℝ (Fin 2)))
    (h_no_vertex_in_interior : ∀ i ∈ A, ∀ v : P,
      (v : EuclideanSpace ℝ (Fin 2)) ∉ arcInterior i)
    (h_same_center_disjoint : ∀ i ∈ A, ∀ j ∈ A,
      center i = center j → i ≠ j →
        arcInterior i ∩ arcInterior j = ∅) :
    ∀ (G : SimpleGraph P) [Fintype G.edgeSet],
      G.edgeFinset = A.image endpoint →
        ∃ D : GeometricArcDrawing G,
          (D.localPairCount : ℝ) ≤ 2 * (P.card : ℝ) ^ 2 := by sorry
