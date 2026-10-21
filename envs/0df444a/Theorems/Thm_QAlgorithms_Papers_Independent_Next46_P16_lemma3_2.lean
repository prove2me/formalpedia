-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P16_lemma3_2
-- name    : QAlgorithms.Papers.Independent.Next46.P16.lemma3_2
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T15:03:05.710975+00:00
-- url     : https://prove2.me/theorems/6f03e59d-4aca-4bf0-90c0-c4a183a7564b
-- title:
--   One-sided form bounds give a continuous Schwartz-valued range
-- statement:
--   Fix $N\ge1$ and let $T$ be any bounded operator on $\mathcal H=L^2(\mathbb R^N)$. Suppose that for every $\alpha,\beta\in\mathbb N_0^N$ the set
--   $$
--   \bigl\{|\langle P^\beta Q^\alpha\psi,T\varphi\rangle|:\psi,\varphi\in\mathcal S(\mathbb R^N),\ \|\psi\|_2,\|\varphi\|_2\le1\bigr\}
--   $$
--   is bounded above. Then $\operatorname{Ran}T\subset\mathcal S(\mathbb R^N)$, and $T:\mathcal H\to\mathcal S(\mathbb R^N)$ is continuous for the full Schwartz topology.
--
--   More precisely, there is a continuous complex-linear map $U:\mathcal H\to\mathcal S(\mathbb R^N)$ whose $L^2$ class is $T v$ for every $v\in\mathcal H$. This expresses both the range and continuity conclusions using actual representatives.
-- source:
--   Schwartz operators, arXiv:1503.04086v1, PDF p. 11, Lemma 3.2

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

/-- Lemma 3.2, PDF p.11: one-sided CanonicalHilbert form bounds imply a continuous
linear lift H -> S(R^n), hence the full range consists of Schwartz vectors. -/
theorem lemma3_2 (n : ℕ) (hn : 0 < n) (T : CanonicalOperator n)
    (hT : ∀ a b : MultiIndex n, BddAbove (operatorFormValues T a 0 b 0)) :
    ∃ U : CanonicalHilbert n →L[ℂ] Schwartz n,
      ∀ v : CanonicalHilbert n, schwartzToHilbert (U v) = T v := by sorry

end QAlgorithms.Papers.Independent.Next46.P16

end
