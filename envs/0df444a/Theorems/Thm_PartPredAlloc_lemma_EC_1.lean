-- Prove2me | Theorems.Thm_PartPredAlloc_lemma_EC_1
-- name    : PartPredAlloc.lemma_EC_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:18:03.280111+00:00
-- url     : https://prove2.me/theorems/b152135d-8512-4708-8948-a78cd8eecfb3
-- title:
--   Lemma EC.1, p.ec1 — $|O_1(\lambda)-\tilde o_1(\lambda)|\ge(5+\sqrt6)\sqrt{n_1\log(1/\epsilon')}$ has probability $\le\epsilon'$
-- statement:
--   Let $n\ge3$ and $p\in(0,1)$. If $\epsilon'\in(0,1/24]$ and $n_1>\frac4{p^2}\log\frac1{\epsilon'}$, then for every $\lambda\in\{1/n,2/n,\dots,n/n\}$
--
--   $$
--   \Pr\Big(\big|O_1(\lambda)-\tilde o_1(\lambda)\big|\ge(5+\sqrt6)\sqrt{n_1\log\tfrac1{\epsilon'}}\Big)\le\epsilon' .
--   $$
--
--   Here $\alpha_{EC.1}=5+\sqrt6$, $\bar\epsilon_{EC.1}=1/24$ and $k_{EC.1}=4$. It is the single-time, single-count version of Lemma 1, obtained from Lemmas EC.2–EC.5 by a union bound and $O_1(\lambda)=Z_1+\zeta_1$.
--
--   Differences from the source:
--   - encoding: probability over the stochastic group S and the random permutation σ_S → prob n p: explicit finite sum with weights p^{|S|}(1−p)^{n−|S|} and σ uniform over the permutations fixing every position outside S; reason: the model has finitely many outcomes; this is its law (§3, p.10), with no measure theory
--   - encoding: λ ∈ {1/n, 2/n, …, 1} → t : ℕ with 1 ≤ t ≤ n and λ = t/n; reason: same set of times
-- source:
--   Hwang, Jaillet, Manshadi, Online Resource Allocation under Partially Predictable Demand, arXiv:1810.00447v1, Lemma EC.1, p.ec1 (PDF 38)

import Mathlib
import Definitions.Def_PartPredAlloc_obsCount

namespace PartPredAlloc

/-- **Lemma EC.1** (Hwang–Jaillet–Manshadi, arXiv:1810.00447v1, Lemma EC.1, p.ec1 = PDF 38). Let
`α_{EC.1} = 5 + √6`, `ε̄_{EC.1} = 1/24` and `k_{EC.1} = 4`. If `ε′ ∈ (0, 1/24]` and
`n₁ > (4/p²) log(1/ε′)`, then for any `λ ∈ {1/n, 2/n, …, n/n}`,
`P(|O₁(λ) − õ₁(λ)| ≥ (5 + √6) √(n₁ log(1/ε′))) ≤ ε′`.

**Formalization Note.** `λ = t/n`, `t ∈ {1, …, n}`; the probability is over the outcome `(S, σ)` of
the partially predictable model. Standing assumptions: `n ≥ 3`, `p ∈ (0, 1)`. -/
theorem lemma_EC_1 {n : ℕ} (hn : 3 ≤ n) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (vI : Fin n → Cust) (ε' : ℝ) (hε0 : 0 < ε') (hε : ε' ≤ 1 / 24)
    (hn1 : (nType1 vI : ℝ) > 4 / p ^ 2 * Real.log (1 / ε'))
    (t : ℕ) (ht1 : 1 ≤ t) (htn : t ≤ n) :
    prob n p (fun _ σ => (5 + Real.sqrt 6) * Real.sqrt ((nType1 vI : ℝ) * Real.log (1 / ε')) ≤
        |(O1 vI σ t : ℝ) - otilde1 p vI t|) ≤ ε' := by sorry

end PartPredAlloc
