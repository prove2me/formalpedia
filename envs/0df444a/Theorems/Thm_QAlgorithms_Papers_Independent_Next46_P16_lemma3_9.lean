-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P16_lemma3_9
-- name    : QAlgorithms.Papers.Independent.Next46.P16.lemma3_9
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T15:07:56.907248+00:00
-- url     : https://prove2.me/theorems/f1e40c95-d761-4022-8756-7030bb27365b
-- title:
--   Bounded compositions with closed operators and their polynomials
-- statement:
--   Let $N\ge1$ and $\mathcal H=L^2(\mathbb R^N)$. Let $A$ be a closed linear operator with its actual linear domain, and let $T\in\mathcal B(\mathcal H)$ satisfy $\operatorname{Ran}T\subset\operatorname{dom}A$. Then
--   $$
--   AT\in\mathcal B(\mathcal H).
--   $$
--   The same conclusion holds when $A$ is any finite polynomial in closed operators. Constants act on all of $\mathcal H$; sums have intersection domains, and $A_1A_2$ has domain $\{v\in\operatorname{dom}A_2:A_2v\in\operatorname{dom}A_1\}$. In each case there exists a bounded operator whose graph is exactly the everywhere-defined composition with $T$.
--
--   This formulation includes a single closed operator as a one-leaf polynomial and does not assume that polynomial products are closed.
-- source:
--   Schwartz operators, arXiv:1503.04086v1, PDF p. 15, Lemma 3.9

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P16

noncomputable section

open MeasureTheory Filter

open QAlgorithms.Papers.Independent.Claimed50.P10 (Configuration)

open QAlgorithms.Papers.Independent.Dependency50.P13 (IsTraceClass)

open scoped BigOperators ENNReal ComplexOrder

namespace QAlgorithms.Papers.Independent.Next46.P16

attribute [local instance] QAlgorithms.Papers.Independent.Next46.P16.canonicalComplexCalculus

attribute [local instance] QAlgorithms.Papers.Independent.Next46.P16.canonicalRealCalculus

attribute [local instance] QAlgorithms.Papers.Independent.Next46.P16.canonicalRealNonUnitalCalculus

/-- Lemma 3.9, PDF p.15, including its polynomial clause: a bounded T with
range in the natural domain of any finite polynomial of closed operators has
bounded composition. A single closed operator is the atom constructor. -/
theorem lemma3_9 (n : ℕ) (hn : 0 < n) (p : ClosedOperatorPolynomial n)
    (T : CanonicalOperator n) (hdom : ∀ x : CanonicalHilbert n, ∃ y, closedPolynomialGraph p (T x) y) :
    ∃ B : CanonicalOperator n, ∀ x y : CanonicalHilbert n,
      closedPolynomialGraph p (T x) y ↔ B x = y := by sorry

end QAlgorithms.Papers.Independent.Next46.P16

end
