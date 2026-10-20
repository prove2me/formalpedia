-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P47_finite_classical_channel_net
-- name    : QAlgorithms.Papers.Independent.Dependency50.P47.finite_classical_channel_net
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T15:46:46.457881+00:00
-- url     : https://prove2.me/theorems/2425fd11-24bc-4f96-967d-b2479f9c2ee4
-- title:
--   Lemma 6: finite uniform net for classical auxiliary channels
-- statement:
--   Fix a positive finite alphabet $X$ of size $n$, a normalized full-support input law $q(x)$ as in Section 4.1, and $\epsilon>0$. Let $\mathcal P$ be the classical channels $X\to C$ with at most $n$ outputs, padded with zero-probability outputs to size $n$. There are a positive integer $M$ and channels $K_1,\ldots,K_M\in\mathcal P$ such that, for every $K\in\mathcal P$, one index $j$ works simultaneously for every finite channel $q(y,z\mid x)$:
--
--   $$
--   \bigl|(I(C;Y)-I(C;Z))-(I(C_j;Y)-I(C_j;Z))\bigr|\le\epsilon.
--   $$
--
--   All quantities use the factored law $q(x)K(c\mid x)q(y,z\mid x)$. Both output alphabets may have arbitrary positive finite sizes. This is a uniform finite net at the fixed input law; the approximating index precedes the output channel.
-- source:
--   On Dimension Bounds for Auxiliary Quantum Systems, arXiv:1207.3911v4, PDF p. 26, Lemma 6: finite uniform net for classical auxiliary channels

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P47

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open MeasureTheory Filter

namespace QAlgorithms.Papers.Independent.Dependency50.P47

open QAlgorithms.Papers.Independent.Information100.P27 (shannon average)

open QAlgorithms.Papers.Independent.Information100.P39 (pushLaw)

open QAlgorithms.Papers.Independent.Information100.P48 (normalize)

open QAlgorithms.Papers.Independent.Information100.P62 (IsProjection)

/-- Lemma 6, PDF pp.11,26: exists net, forall K, exists j, forall output channels. -/
theorem finite_classical_channel_net {n : ℕ} (hn : 0 < n) (p : Law (Fin n))
    (hp : ∀ x, 0 < p.prob x) (eps : ℝ) (heps : 0 < eps) :
    ∃ M : ℕ, 0 < M ∧ ∃ net : Fin M → CChannel (Fin n) (Fin n),
      ∀ K : CChannel (Fin n) (Fin n), ∃ j : Fin M, ∀ O : OutputChannel n,
        |outputClassicalDifference p K O - outputClassicalDifference p (net j) O| ≤ eps := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P47

end
