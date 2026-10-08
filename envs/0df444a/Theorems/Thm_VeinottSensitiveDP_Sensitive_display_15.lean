-- Prove2me | Theorems.Thm_VeinottSensitiveDP_Sensitive_display_15
-- name    : VeinottSensitiveDP.Sensitive.display_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:52:09.62735+00:00
-- url     : https://prove2.me/theorems/68b1a524-e84e-4350-bfd2-e34e573fb1a0
-- title:
--   (15) — the Cesàro limit P* of a substochastic P exists and PP* = P*P = P*P* = P*
-- statement:
--   Let $P$ be an $S\times S$ substochastic matrix (nonnegative entries, row sums at most $1$). Then the Cesàro means of its powers converge,
--   $$P^*=\lim_{N\to\infty}\,(N+1)^{-1}\sum_{i=0}^N P^i,$$
--   and the limit satisfies
--   $$PP^*=P^*P=P^*P^*=P^*.$$
--
--   These identities are used throughout §3: they give $(P-P^*)^n=P^n-P^*$, the nonsingularity of $I-P+P^*$, and $P^*Q=0$ for $Q=P-I$.
--
--   **Formalization Note** $P^*$ is the published `limitMatrix P`; the convergence is stated explicitly. The paper adds that $P^*$ *uniquely* satisfies (15); this is not formalized, since the zero matrix also satisfies the three identities.
-- source:
--   Veinott, Discrete Dynamic Programming with Sensitive Discount Optimality Criteria, Ann. Math. Statist. 40(5):1635–1660 (1969), DOI 10.1214/aoms/1177697379, p. 1642, §3, (15)

import Mathlib
import Definitions.Def_BlackwellDiscreteDP_NearOne_LimitMatrix
import Definitions.Def_VeinottSensitiveDP_Sensitive_Matrix
open Filter Topology Matrix BlackwellDiscreteDP.NearOne

namespace VeinottSensitiveDP.Sensitive

/-- (15): for an `S × S` substochastic matrix `P`, the Cesàro means `(N + 1)⁻¹ Σ_{i=0}^N P^i`
converge to a matrix `P*`, and `PP* = P*P = P*P* = P*`.

Veinott, Discrete Dynamic Programming with Sensitive Discount Optimality Criteria,
Ann. Math. Statist. 40(5):1635–1660 (1969), DOI 10.1214/aoms/1177697379, p. 1642, §3, (15).

**Formalization Note.** `P*` is the published `limitMatrix P` (a `limUnder`), and `cesaroMean P N`
is exactly `(N + 1)⁻¹ Σ_{i=0}^N P^i`; the first conjunct says the limit exists. The paper's
"P* uniquely satisfies (15)" is not formalized: the zero matrix also satisfies the three
equations, so the uniqueness cannot be stated literally. -/
theorem display_15 {St : Type} [Fintype St] [DecidableEq St] (P : Matrix St St ℝ)
    (hP : IsSubstochastic P) :
    Tendsto (cesaroMean P) atTop (𝓝 (limitMatrix P)) ∧
      P * limitMatrix P = limitMatrix P ∧ limitMatrix P * P = limitMatrix P ∧
      limitMatrix P * limitMatrix P = limitMatrix P := by sorry

end VeinottSensitiveDP.Sensitive
