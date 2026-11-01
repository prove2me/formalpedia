-- Prove2me | Theorems.Thm_SponsoredAssort_g3_singleton
-- name    : SponsoredAssort.g3_singleton
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:52:46.888809+00:00
-- url     : https://prove2.me/theorems/92f8f19d-4e00-4aa3-9aff-15d390cce832
-- title:
--   Appendix G.3, OA p.38 — at $v(\epsilon)$ first best is $[n]$ and every singleton gets $1/n+o(1)$ of it
-- statement:
--   Let $r>0$ and $v(\epsilon)=(\epsilon,(r_1/r_2)\epsilon,\dots,(r_1/r_n)\epsilon)$. For every $\eta>0$ there is $\epsilon_0>0$ such that for all $0<\epsilon<\epsilon_0$:
--
--   1. $S^{FB}(v(\epsilon))=\{1,\dots,n\}$, i.e. $R(\{1,\dots,n\},v(\epsilon))=R(m^{FB},v(\epsilon))$;
--   2. for every seller $i$,
--   $$
--   \Big(\frac1n-\eta\Big)R(m^{FB},v(\epsilon))\ \le\ R(\{i\},v(\epsilon))\ \le\ \Big(\frac1n+\eta\Big)R(m^{FB},v(\epsilon)).
--   $$
--
--   That is, $R(\{i\},v(\epsilon))/R(\{1,\dots,n\},v(\epsilon))=1/n+o(1)$ as $\epsilon\to0$: a mechanism that displays a single seller at $v(\epsilon)$ has ratio close to $1/n$ there.
--
--   Differences from the source:
--   - encoding: $=1/n+o(1)$ as $\epsilon\to0$ → two-sided bound with tolerance $\eta$ for $0<\epsilon<\epsilon_0$, uniform in $i$; reason: definition of $o(1)$
--   - encoding: $S^{FB}(v(\epsilon))=\{1,\dots,n\}$ → $R([n],v(\epsilon))=\max_S R(S,v(\epsilon))$; reason: $S^{FB}$ is a maximizer
--   - generalization: revenues with $r_i/r_{i+1}\ge n$ (context of the proof) → any $r>0$; reason: the computation uses only $r>0$; it specializes
-- source:
--   Balseiro, Désir, Incentive-Compatible Assortment Optimization for Sponsored Products, SSRN 3821382 (Feb. 21, 2022), Appendix G.3, proof of Proposition 5.4, OA p.38

import Mathlib
import Definitions.Def_SponsoredAssort_firstBest
import Definitions.Def_SponsoredAssort_pointEps

open scoped NNReal

namespace SponsoredAssort

/-- **Appendix G.3, singleton case** (Balseiro, Désir, SSRN 3821382 (Feb. 21, 2022), proof of
Proposition 5.4, OA p.38). Let `r > 0` and `v(ε) = (ε, (r₁/r₂)ε, …, (r₁/rₙ)ε)`. For `ε` small enough
`S^FB(v(ε)) = {1, …, n}`, and for every seller `i`,
`R({i}, v(ε)) / R({1, …, n}, v(ε)) = 1/n + o(1)` as `ε → 0`.

**Formalization Note.** `S^FB(v(ε)) = [n]` is stated as `R([n], v(ε)) = R(m^FB, v(ε))`. The `o(1)`
is stated with an explicit tolerance: for every `η > 0` there is `ε₀ > 0` such that, for all
`0 < ε < ε₀` and every `i`, `(1/n − η)·R(m^FB, v(ε)) ≤ R({i}, v(ε)) ≤ (1/n + η)·R(m^FB, v(ε))`;
`ε₀` is uniform in `i`. -/
theorem g3_singleton {n : ℕ} [NeZero n] (r : Fin n → ℝ) (hr : ∀ i, 0 < r i) :
    ∀ η : ℝ, 0 < η → ∃ ε₀ : ℝ≥0, 0 < ε₀ ∧ ∀ ε : ℝ≥0, 0 < ε → ε < ε₀ →
      welfare r Finset.univ (pointEps r ε) = firstBest r (pointEps r ε) ∧
      ∀ i : Fin n,
        (1 / (n : ℝ) - η) * firstBest r (pointEps r ε) ≤ welfare r {i} (pointEps r ε) ∧
        welfare r {i} (pointEps r ε) ≤ (1 / (n : ℝ) + η) * firstBest r (pointEps r ε) := by sorry

end SponsoredAssort
