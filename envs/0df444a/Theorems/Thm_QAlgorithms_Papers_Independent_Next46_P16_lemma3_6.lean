-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P16_lemma3_6
-- name    : QAlgorithms.Papers.Independent.Next46.P16.lemma3_6
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T15:06:51.840295+00:00
-- url     : https://prove2.me/theorems/c736bfef-865c-493f-a09a-ce08d77fff28
-- title:
--   Every Schwartz operator is trace class
-- statement:
--   Let $N\ge1$ and $\mathcal H=L^2(\mathbb R^N)$. A bounded operator $T$ is Schwartz if, for every four multi-indices $\alpha,\alpha',\beta,\beta'$, the form $\langle P^\beta Q^\alpha\psi,T P^{\beta'}Q^{\alpha'}\varphi\rangle$ is bounded on the two Schwartz unit balls. Then
--   $$
--   T\in\mathcal T(\mathcal H),\qquad \operatorname{Tr}\sqrt{T^*T}<\infty.
--   $$
--   The claim applies to all Schwartz operators, without positivity or trace normalization. It provides trace-class membership for the canonical Schwartz operator space.
-- source:
--   Schwartz operators, arXiv:1503.04086v1, PDF p. 13, Lemma 3.6

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

/-- Lemma 3.6, PDF p.13: every Schwartz operator is trace class. -/
theorem lemma3_6 (n : ℕ) (hn : 0 < n) (T : CanonicalOperator n)
    (hT : IsSchwartzOperator T) : IsTraceClass T := by sorry

end QAlgorithms.Papers.Independent.Next46.P16

end
