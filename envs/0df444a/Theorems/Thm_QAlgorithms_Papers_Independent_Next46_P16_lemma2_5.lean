-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P16_lemma2_5
-- name    : QAlgorithms.Papers.Independent.Next46.P16.lemma2_5
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T15:01:53.356693+00:00
-- url     : https://prove2.me/theorems/17e671b6-8436-44fb-840c-632e1266b951
-- title:
--   Finite sums of Schwartz dyads are dense in every finite Schatten class
-- statement:
--   Fix $N\ge1$ and an integer $p\ge1$. Let $\mathcal T_p(\mathcal H)$ be the Schatten class on $\mathcal H=L^2(\mathbb R^N)$, with $\|A\|_p=(\operatorname{Tr}|A|^p)^{1/p}$. For every $T\in\mathcal T_p(\mathcal H)$ and every $\varepsilon>0$, there exist a finite $m\ge0$ and Schwartz functions $f_k,g_k$ such that
--   $$
--   \left\|T-\sum_{k=1}^m |f_k\rangle\langle g_k|\right\|_p<\varepsilon.
--   $$
--   The dyad sends $v$ to $\langle g_k,v\rangle f_k$. This is density in the full Schatten class; no positivity or normalization is imposed.
-- source:
--   Schwartz operators, arXiv:1503.04086v1, PDF p. 7, Lemma 2.5

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

/-- Lemma 2.5, PDF pp.7--8: all finite Schwartz dyads are dense in every
finite positive-integer Schatten class, with no positivity assumption. -/
theorem lemma2_5 (n : ℕ) (hn : 0 < n) (p : ℕ) (hp : 1 ≤ p)
    (T : CanonicalOperator n) (hT : IsSchatten p T) :
    ∀ eps : ℝ, 0 < eps → ∃ (m : ℕ) (f g : Fin m → Schwartz n),
      integerSchattenNorm p (T - finiteSchwartzSum f g) < ENNReal.ofReal eps := by sorry

end QAlgorithms.Papers.Independent.Next46.P16

end
