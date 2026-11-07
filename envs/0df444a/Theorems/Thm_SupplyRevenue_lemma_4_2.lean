-- Prove2me | Theorems.Thm_SupplyRevenue_lemma_4_2
-- name    : SupplyRevenue.lemma_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:48:21.6372+00:00
-- url     : https://prove2.me/theorems/0a1982dc-d1ca-423b-8037-c224d5bc7cbd
-- title:
--   Lemma 4.2 — cost-weighted payment recovery
-- statement:
--   Let a source price law for one buyer have full-stock demand $X$, payment $s=p(X)$, marginals $x_j$, and $R_H=E[s\mathbf 1\{s\le H\}]$, where $H,\ell>0$. Assume the buyer is XOS with $0<\eta\le 1/2$, or in $\mathcal V_d$ with $0<\eta\le 1/(2d)$. Put
--
--   $$k=\lceil\log_2(1+H/(\eta\ell))\rceil,\qquad\alpha=\frac{1-\eta}{8(1+\eta k)}.\tag{7}$$
--
--   For every $c\ge 0$ there is a finite mixture of full offers, independent of type and of the stock, such that against every stock law with item absence at most $\eta$,
--
--   $$E[P-c(Q)]\ge\alpha\Bigl(R_H-2\ell\sum_j x_j\Bigr)-4\alpha\,c\cdot x,\tag{8}$$
--
--   where $Q,P$ are the actual allocation and payment.
--
--   This is the local response that feeds Lemma 2.2 and Lemma 5.1.
--
--   Differences from the source:
--   - reading: "a fixed residual bundle order" → any injective rank `tie : Finset (Fin m) ↪ ℕ`, one per statement; reason: R3: the order is unspecified on the page, so every statement holds for every rank
--   - reading: a source of offers → one finite mixture of offers per buyer; reason: R4: p.2 "finite-mixture approximation"; each offer gives a point of a bounded finite-dimensional set, so arbitrary laws add nothing to the supremum
--   - generalization: "a full-offer law independent of type and realized stock" → one law serving every good stock law: the law is quantified before the stock law; reason: the page's construction depends on $c,H,\ell,\eta$ and the source only; taking the law after the stock law specializes this to the page's reading
--   - generalization: $H,\ell$ of the calibration (2) → any $H,\ell>0$; reason: the lemma and its proof use only $H,\ell>0$; (2) gives positive $H,\ell$ for $R,\delta>0$, so it is an instance
--   - generalization: $\mathcal V_d$ with the standing $1\le d\le m$ (p.3) → any $d\ge 1$; reason: the proof's union bound $1-d\eta\ge 1/2$ uses only $\eta\le 1/(2d)$; $d\le m$ is an instance
--   - reading: "For XOS buyers", "for $\mathcal V_d$ buyers" → every supported type is in the class; reason: R10: unsupported types do not affect any expectation
-- source:
--   Mahboub, Rahgoshay, Supply-Sensitive Revenue Recovery under Unknown Buyer Order (manuscript, sha256 c04de641…), Lemma 4.2, p.9, (7), (8)

import Mathlib
import Definitions.Def_SupplyRevenue_Classes
import Definitions.Def_SupplyRevenue_CapRev
import Definitions.Def_SupplyRevenue_Local

namespace SupplyRevenue

/-- Mahboub, Rahgoshay, *Supply-Sensitive Revenue Recovery under Unknown Buyer Order* (manuscript, sha256 c04de641…),
Lemma 4.2, p.9 (Cost-weighted payment recovery), with (7) and (8).

**Formalization Note** `k` is the ladder length (7), not the `4^L` of §9; `c` is the cost vector. `H, ℓ > 0` are arbitrary.
The offer law `τ` is quantified **before** the stock law: it depends on `c, H, ℓ, η` and the source only, which is the
stronger form and what the page's proof gives. Item absence at most `η` is `GoodStock`. `Q, P` are the actual allocation
and payment. A `d`-demand buyer has `1 ≤ d`. -/
theorem lemma_4_2 {m : ℕ} (hm : 0 < m) (tie : Tie m) (b : Buyer m) (σ : Mix (Offer m))
    (H ℓ η : ℝ) (hH : 0 < H) (hℓ : 0 < ℓ)
    (hclass : (b.InClass IsXOS ∧ 0 < η ∧ η ≤ 1 / 2) ∨
      ∃ d : ℕ, 1 ≤ d ∧ b.InClass (InV d) ∧ 0 < η ∧ η ≤ 1 / (2 * (d : ℝ)))
    (k : ℕ) (hk : k = ⌈Real.logb 2 (1 + H / (η * ℓ))⌉₊)
    (α : ℝ) (hα : α = (1 - η) / (8 * (1 + η * (k : ℝ))))
    (c : Fin m → ℝ) (hc : ∀ j, 0 ≤ c j) :
    ∃ τ : Mix (Offer m), ∀ μ : Lottery m, GoodStock μ η →
      α * (sourceStat tie b σ (fun s => if s ≤ H then s else 0) -
          2 * ℓ * ∑ j, sourceMarginal tie b σ j) -
        4 * α * ∑ j, c j * sourceMarginal tie b σ j ≤
      localE tie b τ μ fun o Q => o.pay Q - ∑ j ∈ Q, c j := by sorry

end SupplyRevenue
