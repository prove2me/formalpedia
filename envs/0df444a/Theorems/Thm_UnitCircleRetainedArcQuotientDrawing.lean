-- Prove2me | Theorems.Thm_UnitCircleRetainedArcQuotientDrawing
-- name    : UnitCircleRetainedArcQuotientDrawing
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T18:42:29.336983+00:00
-- url     : https://prove2.me/theorems/c5ac5ef6-4dca-40fa-a646-6c91703c1c79
-- title:
--   Unit Circle Retained Arc Quotient Drawing
-- statement:
--   Let $P\subset\mathbb{R}^2$ be finite, and let
--   $$
--     R=\{p\in P: |P\cap \operatorname{UnitCircle}(p)|\ge3\}.
--   $$
--   There are a finite type $\iota$, a finite set $A\subseteq\iota$, and an
--   endpoint map $\epsilon:\iota\to\operatorname{Sym}^2(P)$ such that
--   $$
--     |A|=\sum_{p\in R}|P\cap\operatorname{UnitCircle}(p)|,
--   $$
--   for every $a\in A$ the unordered endpoint pair $\epsilon(a)$ is not
--   diagonal, and every endpoint pair in the image $\epsilon(A)$ has at most two
--   preimages in $A$.  Moreover, for every finite simple graph $G$ on vertex
--   set $P$ whose edge set is exactly $\epsilon(A)$, there is a finite
--   geometric-arc drawing $D$ of $G$, in the sense of
--   `GeometricArcDrawing`, with
--   $$
--     D.\operatorname{localPairCount}\le 2|P|^2 .
--   $$
--
--   **Formalization Note** This node is ported from the Trellis formalization of the crossing lemma and its consequences ([wpegden/crossing-consequences](https://github.com/wpegden/crossing-consequences), commit `8769d142`, W. Pegden, Apache-2.0); the statement is the Trellis node `UnitCircleRetainedArcQuotientDrawing`.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/UnitCircleRetainedArcQuotientDrawing.lean#L1-L38

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Definitions.Def_GeometricArcDrawing
import Definitions.Def_UnitCircle

open Classical
open scoped BigOperators
open scoped Real
noncomputable section

lemma UnitCircleRetainedArcQuotientDrawing
    (P : Finset (EuclideanSpace ℝ (Fin 2))) :
    ∃ (ι : Type) (instF : Fintype ι) (instD : DecidableEq ι)
      (A : Finset ι) (endpoint : ι → Sym2 P),
      (A.card : ℝ) =
          ∑ p ∈ P.filter
            (fun p => 3 ≤ (P.filter (fun q => q ∈ UnitCircle p)).card),
            ((P.filter (fun q => q ∈ UnitCircle p)).card : ℝ) ∧
        (∀ i ∈ A, ¬ (endpoint i).IsDiag) ∧
          (∀ e ∈ A.image endpoint,
            (A.filter (fun i => endpoint i = e)).card ≤ 2) ∧
            (∀ (G : SimpleGraph P) [Fintype G.edgeSet],
              G.edgeFinset = A.image endpoint →
                ∃ D : GeometricArcDrawing G,
                  (D.localPairCount : ℝ) ≤ 2 * (P.card : ℝ) ^ 2) := by sorry
