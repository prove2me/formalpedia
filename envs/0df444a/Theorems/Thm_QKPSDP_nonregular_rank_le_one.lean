-- Prove2me | Theorems.Thm_QKPSDP_nonregular_rank_le_one
-- name    : QKPSDP.nonregular_rank_le_one
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:49:48.185783+00:00
-- url     : https://prove2.me/theorems/8f85e211-2f99-4456-9439-05912b1fcac8
-- title:
--   §4.3, p.17 — every non-regular point of $\mathcal K_{n,r}$ has rank at most 1
-- statement:
--   Suppose $(a,\tau)$ satisfies Assumption 1. If $R \in \mathcal K_{n,r}$ is not regular, then
--
--   $$
--   \operatorname{rank}(R) \le 1 .
--   $$
--
--   In particular $\operatorname{rank}(R) \le r - 2$ whenever $r \ge 3$, so non-regular points always satisfy the rank hypothesis of Lemma 4.8, which is why Lemma 4.10 needs to treat only regular points.
--
--   Differences from the source:
--   - encoding: Assumption 1 (p.1), in the standing setting "we consider the nontrivial case where n > 1" (p.1) → Assumption1 a τ includes 1 < n; reason: the paper's standing assumption; for n ≥ 1 it follows from Assumption 1, so it only excludes n = 0, which the paper excludes
--   - encoding: indices from 1; e₁ ∈ ℝʳ the first unit vector → Fin n, Fin r from 0; e1 r = Pi.single 0 1 with [NeZero r]; reason: e₁ needs r ≥ 1, which the hypothesis r ≥ 3 (or the page's R ∈ ℝ^{n×r} with e₁) already gives; same instances
--   - encoding: R regular: LICQ holds at R (p.6) → IsRegular: (5) diag(μ)(2R − ee₁⊤) + λa(2a⊤R − τe₁⊤) = 0 has only the solution μ = 0, λ = 0; reason: (5) is the linear dependence relation of the n + 1 constraint gradients (p.7); same instances
--   - generalization: "rank(R) ≤ 1 ≤ r − 2 for any r ≥ 3" → rank(R) ≤ 1 for every r ≥ 1 (no hypothesis r ≥ 3); reason: the bound rank(R) ≤ 1 comes from Proposition 3.1, which holds for every r ≥ 1; the inequality 1 ≤ r − 2 is arithmetic in r ≥ 3, so the statement specializes to the page's
-- source:
--   Tang & Toh, A feasible method for solving an SDP relaxation of the quadratic knapsack problem, arXiv:2303.06599v1, §4.3, paragraph before Theorem 4.11, p.17

import Mathlib
import Definitions.Def_QKPSDP_Assumption1
import Definitions.Def_QKPSDP_K
import Definitions.Def_QKPSDP_IsRegular

namespace QKPSDP

/-- Tang & Toh, arXiv:2303.06599v1, §4.3, p.17 (paragraph before Theorem 4.11): "from
Proposition 3.1, the rank of any non-regular point `R` of `K_{n,r}` already satisfies the
condition that `rank(R) ≤ 1 ≤ r − 2` for any `r ≥ 3`."

**Formalization Note** The conclusion is `rank(R) ≤ 1`; the second inequality `1 ≤ r − 2` is
arithmetic in `r ≥ 3` and is not restated. Like Proposition 3.1, the claim needs only `r ≥ 1`
(`[NeZero r]`). -/
theorem nonregular_rank_le_one {n r : ℕ} [NeZero r] (a : Fin n → ℝ) (τ : ℝ)
    (ha : Assumption1 a τ) (R : Matrix (Fin n) (Fin r) ℝ) (hR : R ∈ K a τ)
    (hnreg : ¬ IsRegular a τ R) : R.rank ≤ 1 := by sorry

end QKPSDP
