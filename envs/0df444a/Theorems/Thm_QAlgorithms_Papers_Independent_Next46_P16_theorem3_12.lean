-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P16_theorem3_12
-- name    : QAlgorithms.Papers.Independent.Next46.P16.theorem3_12
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T15:08:46.295894+00:00
-- url     : https://prove2.me/theorems/4852e553-1c89-4e35-9798-be985a256e4f
-- title:
--   Both ranges characterize Schwartz operators and their topology
-- statement:
--   Fix $N\ge1$ and the canonical space $\mathcal H=L^2(\mathbb R^N)$. Define Schwartz operators by Hilbert boundedness of the four-index forms, and give their space its original form-seminorm topology. For every $T\in\mathcal B(\mathcal H)$,
--   $$
--   T\in\mathcal S(\mathcal H)\iff \operatorname{Ran}T\subset\mathcal S(\mathbb R^N)\ \text{and}\ \operatorname{Ran}T^*\subset\mathcal S(\mathbb R^N).
--   $$
--   For $T\in\mathcal S(\mathcal H)$ and $\alpha,\beta\in\mathbb N_0^N$, the following finite seminorms together induce that same topology:
--   $$
--   \|T\|_{\alpha,0,\beta,0}=\sup_{v\in\mathcal H,\ \|v\|_2\le1}\|Tv\|_{\alpha,\beta},\qquad
--   \|T\|_{0,\alpha,0,\beta}=\sup_{v\in\mathcal H,\ \|v\|_2\le1}\|T^*v\|_{\alpha,\beta}.
--   $$
--   Here $\|[f]\|_{\alpha,\beta}=\|Q^\alpha P^\beta f\|_2$ for the unique Schwartz representative. Both range clauses and the topology statement are retained.
-- source:
--   Schwartz operators, arXiv:1503.04086v1, PDF p. 17, Theorem 3.12

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

/-- Theorem 3.12, PDF pp.17--18: both ranges characterize Schwartz operators;
the left/right seminorms induce their original topology, with the exact full
Hilbert-unit-ball supremum formulas from the display on p.17. -/
theorem theorem3_12 (n : ℕ) (hn : 0 < n) :
    (∀ T : CanonicalOperator n, IsSchwartzOperator T ↔
      (∀ v : CanonicalHilbert n, IsSchwartzVector (T v)) ∧
      (∀ v : CanonicalHilbert n, IsSchwartzVector (T.adjoint v))) ∧
    schwartzOperatorTopology n = oneSidedTopology n ∧
    (∀ (T : SchwartzOperator n) (a b : MultiIndex n),
      BddAbove (rangeSeminormValues T.val a b) ∧
      BddAbove (rangeSeminormValues T.val.adjoint a b) ∧
      operatorFormBound T.val a 0 b 0 = sSup (rangeSeminormValues T.val a b) ∧
      operatorFormBound T.val 0 a 0 b = sSup (rangeSeminormValues T.val.adjoint a b)) := by sorry

end QAlgorithms.Papers.Independent.Next46.P16

end
