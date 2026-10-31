-- Prove2me | Theorems.Thm_WarrantyMatch_eq_EC_3
-- name    : WarrantyMatch.eq_EC_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:38:07.725205+00:00
-- url     : https://prove2.me/theorems/8aba3faa-b168-4327-9bd3-16ef4742e7fe
-- title:
--   (EC.3) — $|\Pr(D_t\le k)-\Pr(D_{t-l-z}\le k)|\le(l+z)\epsilon$
-- statement:
--   Let $(D_u)_{u\in\mathbb Z}$ be integer-valued functions on a probability space $(\Omega,P)$ that satisfy the Kolmogorov–Smirnov drift condition (6) with parameter $\varepsilon$ up to period $t$, that is, $|P(D_{u+1}\le k)-P(D_u\le k)|\le\varepsilon$ for all $u$ with $u+1\le t$ and all $k\in\mathbb Z$. Then for every lead time $l\in\mathbb N$, every $z\in\mathbb N$ and every $k\in\mathbb Z$,
--   $$
--   \bigl|P(D_t\le k)-P(D_{t-l-z}\le k)\bigr|\le(l+z)\,\varepsilon .
--   $$
--
--   The bound turns the per-period drift into a KS distance between the date of a customer in period $t$ and the date of a device returned $l+z$ periods earlier, which is the input of Lemma EC.1 in the proof of Proposition 1.
--
--   **Formalization Note** The index $t-l-z$ is integer subtraction ($l$ and $z$ cast to $\mathbb Z$).
--
--   Differences from the source:
--   - encoding: maximum over k = 1, …, m → every k ∈ ℤ; reason: the dates lie in [1, m] in the paper, where the two conditions coincide
--   - generalization: random variables D_u satisfying (6) for all t, z ≥ 1 the inventory time → arbitrary integer-valued functions (no measurability) satisfying (6) only for u + 1 ≤ t, any z ∈ ℕ including 0; reason: the triangle-inequality argument uses only (6) at u = t − l − z, …, t − 1; the paper's setting is a special case
-- source:
--   Calmon–Graves–Lemmens, Warranty Matching in a Consumer Electronics Closed-Loop Supply Chain, INSEAD WP 2020/03/TOM (SSRN 3357683), §EC.2, proof of Proposition 1, eq. (EC.3), p.ec4

import Mathlib
import Definitions.Def_WarrantyMatch_Model

open MeasureTheory

namespace WarrantyMatch

/-- **(EC.3)** (KS telescoping). If the termination dates satisfy the drift condition (6) up to
period `t`, then for every lead time `l`, every `z ∈ ℕ` and every date `k`,
`|Pr(D_t ≤ k) − Pr(D_{t−l−z} ≤ k)| ≤ (l + z) ε`.
Calmon–Graves–Lemmens, *Warranty Matching in a Consumer Electronics Closed-Loop Supply Chain*,
INSEAD WP 2020/03/TOM (SSRN 3357683), §EC.2, proof of Proposition 1, eq. (EC.3), p.ec4.

**Formalization Note** `k` ranges over all integers (the paper's `k = 1, …, m`). The indices
`t − l − z` are integers (`l, z` cast to `ℤ`), never truncated. No measurability, independence
or support condition is assumed: the bound follows from (6) alone. -/
theorem eq_EC_3 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (D : ℤ → Ω → ℤ) (ε : ℝ) (t : ℤ) (l : ℕ) (hdrift : KSDrift P D ε t) (z : ℕ) (k : ℤ) :
    |(P {ω | D t ω ≤ k}).toReal - (P {ω | D (t - l - z) ω ≤ k}).toReal| ≤
      ((l : ℝ) + z) * ε := by sorry

end WarrantyMatch
