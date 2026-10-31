-- Prove2me | Theorems.Thm_SinkhornHall_log_kappa_sinkhorn_le
-- name    : SinkhornHall.log_kappa_sinkhorn_le
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:38:28.637549+00:00
-- url     : https://prove2.me/theorems/4a8df223-fbb3-4dbc-a720-64fc3b232328
-- title:
--   Proof of Theorem 4.1 — $\log\kappa \le \log(mA_{\max}) - 4\ell/n^2$, hence $\kappa\le A_{\min}$ after $(1/4)n^2\log(mA_{\max}/A_{\min})$ iterations
-- statement:
--   Let $A$ be a nonnegative $n\times n$ matrix with no zero row or column whose support graph has no perfect matching, with $(r,c)=(\mathbf 1,\mathbf 1)$. Let $m$ be the number of nonzero entries of $A$, $A_{\max}$ its largest entry and $A_{\min}$ its least positive entry, and let $(x^{(\ell)},y^{(\ell)})$ be the scaling vectors after step 0 and $\ell$ repetitions of step 1 of the algorithm. Then:
--
--   1. for every $\ell$,
--   $$\log\kappa\big(x^{(\ell)},y^{(\ell)}\big)\ \le\ \log(mA_{\max})-\frac{4\ell}{n^2};$$
--   2. if $\ell\ge\frac14 n^2\log\frac{mA_{\max}}{A_{\min}}$, then $\kappa\big(x^{(\ell)},y^{(\ell)}\big)\le A_{\min}$.
--
--   The second clause is the certificate condition of Corollary 2.6, which the rounding step turns into a Hall blocker.
--
--   Differences from the source:
--   - reading: §4 standing assumptions (p.15): G = G(A) for a nonnegative n × n matrix A, no isolated node, n = |U| = |V|, (r, c) = (1, 1) → A : Matrix (Fin n) (Fin n) ℝ with hA, hrow, hcol, and marginals 1; reason: stated once at the top of §4 and in force for Theorem 4.1 and its proof
--   - reading: 'Suppose that G has no perfect matching' → hpm : ¬ HasPerfectMatching A; reason: the iteration bound is proved under Theorem 4.1's hypothesis
--   - reading: log (base not named) → Real.log (natural logarithm); reason: the constants 1/2 (Pinsker), 4/n² and 1/4 are derived in the natural log
--   - reading: 'log κ(x, y) ≤ log κ(1, 1) − 4ℓ/n² ≤ log mA_max − …' → clause 1 states the bound with log(mA_max), the next link of the chain; reason: κ(1, 1) = ∥A∥₁ ≤ mA_max is the first sentence of the proof
--   - encoding: m, the number of nonzero elements of A → numEdges A; reason: §2 uses m for the column count
--   - encoding: the scaling vectors after ℓ iterations → sinkhorn A ℓ, where ℓ = 0 is the state after step 0; reason: Lean convention for the algorithm's state
-- source:
--   Hayashi–Hirai–Sakabe, Finding Hall blockers by matrix scaling, arXiv:2204.07425v2, proof of Theorem 4.1, pp.15–16 ('Notice κ(1, 1) = ∥A∥₁ ≤ mA_max' and 'Therefore, after ℓ ≥ (1/4)n² log mA_max/A_min iterations …')

import Mathlib
import Definitions.Def_SinkhornHall_Model
import Definitions.Def_SinkhornHall_Analysis

open Finset

namespace SinkhornHall

/-- **The iteration bound of Theorem 4.1's proof.**
Hayashi–Hirai–Sakabe, arXiv:2204.07425v2, proof of Theorem 4.1, pp.15–16: "Notice κ(1, 1) = ∥A∥₁ ≤
mA_max." … "Therefore, after ℓ ≥ (1/4)n² log mA_max/A_min iterations, we have log κ(x, y) ≤
log κ(1, 1) − 4ℓ/n² ≤ log mA_max − log mA_max/A_min ≤ log A_min."

Setting of §4 (p.15): `A` nonnegative `n × n` with no zero row or column, `(r, c) = (1, 1)`, `G(A)`
without a perfect matching; `m` is the number of nonzero entries of `A`.

Clause 1: for every `ℓ`, the pair `(x, y)` after step 0 and `ℓ` repetitions of step 1 satisfies
`log κ(x, y) ≤ log(m A_max) − 4ℓ/n²`. Clause 2: if `ℓ ≥ (1/4) n² log(m A_max / A_min)` then
`κ(x, y) ≤ A_min`.

**Formalization Note.** `m` is `numEdges A`; `log` is `Real.log`; `(x, y) = sinkhorn A ℓ`, where
`ℓ = 0` is the state right after step 0, `(1, C(1))`. -/
theorem log_kappa_sinkhorn_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (hrow : ∀ i, ∃ j, 0 < A i j) (hcol : ∀ j, ∃ i, 0 < A i j)
    (hpm : ¬ HasPerfectMatching A) :
    (∀ ℓ : ℕ, Real.log (kappa A 1 1 (sinkhorn A ℓ).1 (sinkhorn A ℓ).2) ≤
        Real.log ((numEdges A : ℝ) * Amax A) - 4 * (ℓ : ℝ) / (n : ℝ) ^ 2) ∧
      ∀ ℓ : ℕ, (1 / 4 : ℝ) * (n : ℝ) ^ 2 * Real.log ((numEdges A : ℝ) * Amax A / Amin A) ≤ ℓ →
        kappa A 1 1 (sinkhorn A ℓ).1 (sinkhorn A ℓ).2 ≤ Amin A := by sorry

end SinkhornHall
