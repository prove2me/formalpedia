-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P47_exact_minimax_exchange
-- name    : QAlgorithms.Papers.Independent.Dependency50.P47.exact_minimax_exchange
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T15:47:32.971335+00:00
-- url     : https://prove2.me/theorems/08fe003b-a933-46f2-a7d1-7b3bb1f17a9a
-- title:
--   Lemma 7: exact max–min exchange
-- statement:
--   Fix a full-support law $q(x)$ on a nonempty finite alphabet $X$, a finite cq channel $X\to F$, and a nonempty finite list of classical channels $X\to C_j$ with at most $|X|$ outputs. For a probability vector $\lambda$ and a channel $Q=q(y,z\mid x)$ with arbitrary positive finite output alphabets, put
--
--   $$
--   L(\lambda,Q)=I(F;Y)-I(F;Z)-\sum_j\lambda_j(I(C_j;Y)-I(C_j;Z)).
--   $$
--
--   There are actual choices $\lambda_*,Q_*$ such that $L(\lambda_*,Q)\le L(\lambda_*,Q_*)\le L(\lambda,Q_*)$ for every $Q,\lambda$. In particular,
--
--   $$
--   \min_\lambda\max_Q L(\lambda,Q)=\max_Q\min_\lambda L(\lambda,Q),
--   $$
--
--   with both sides attained. The two outputs may retain the same independent flag, so their alphabet sizes are not fixed. The saddle formulation makes the extremizers explicit and avoids real supremum or infimum defaults.
-- source:
--   On Dimension Bounds for Auxiliary Quantum Systems, arXiv:1207.3911v4, PDF p. 26, Lemma 7: exact max–min exchange

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P47

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open MeasureTheory Filter

namespace QAlgorithms.Papers.Independent.Dependency50.P47

open QAlgorithms.Papers.Independent.Information100.P27 (shannon average)

open QAlgorithms.Papers.Independent.Information100.P39 (pushLaw)

open QAlgorithms.Papers.Independent.Information100.P48 (normalize)

open QAlgorithms.Papers.Independent.Information100.P62 (IsProjection)

/-- Lemma 7, PDF pp.11–12,26: exact attained min-max = max-min, expressed as a saddle point.
Both extremizers are present, so no default-valued real extrema occur. -/
theorem exact_minimax_exchange {n d M : ℕ} (hn : 0 < n) (hd : 0 < d) (hM : 0 < M)
    (p : Law (Fin n)) (hp : ∀ x, 0 < p.prob x) (Q : QChannel (Fin n) (Fin d))
    (K : Fin M → CChannel (Fin n) (Fin n)) :
    ∃ w : Law (Fin M), ∃ O : OutputChannel n,
      (∀ P : OutputChannel n, minimaxPayoff p Q K w P ≤ minimaxPayoff p Q K w O) ∧
      (∀ v : Law (Fin M), minimaxPayoff p Q K w O ≤ minimaxPayoff p Q K v O) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P47

end
