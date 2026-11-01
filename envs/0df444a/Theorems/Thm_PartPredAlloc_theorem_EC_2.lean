-- Prove2me | Theorems.Thm_PartPredAlloc_theorem_EC_2
-- name    : PartPredAlloc.theorem_EC_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:16:30.953269+00:00
-- url     : https://prove2.me/theorems/284f6c07-26fa-48aa-bf6d-57922d55b5ca
-- title:
--   Theorem EC.2, p.ec2 — hypergeometric tail bounds (Hush and Scovel 2005)
-- statement:
--   Let $K\sim\mathrm{Hyper}(n_1,n,m)$ count the defectives selected when $n_1$ items are drawn without replacement from a population of $n$ items of which $m$ are defective, and let $\gamma\ge2$. Then
--
--   $$
--   \Pr\big(K-\mathbb E[K]>\gamma\big)<e^{-2\alpha_{n_1,n,m}(\gamma^2-1)}\quad\text{and}\quad \Pr\big(K-\mathbb E[K]<-\gamma\big)<e^{-2\alpha_{n_1,n,m}(\gamma^2-1)},
--   $$
--
--   where
--
--   $$
--   \alpha_{n_1,n,m}=\max\Big\{\frac1{n_1+1}+\frac1{n-n_1+1},\ \frac1{m+1}+\frac1{n-m+1}\Big\}.
--   $$
--
--   The paper cites this from D. Hush and C. Scovel, *Concentration of the hypergeometric distribution*, Statistics & Probability Letters 75(2) (2005) 127–132, and uses it to bound $Z_1$ around its conditional mean (Lemma EC.4).
--
--   **Formalization Note** In Lean the population is $N$, the draws $d$ and the defectives $m$, with $d,m\le N$; $\mathbb E[K]=dm/N$, and each probability is a sum of the hypergeometric mass function over the values $k\in\{0,\dots,\min(d,m)\}$ in the event.
--
--   Differences from the source:
--   - encoding: K ∼ Hyper(n₁, n, m); P(K − E[K] > γ) → draws d, population N, defectives m (d, m ≤ N); sum of hyperPMF N d m k over k ≤ min(d, m) with k − dm/N > γ; reason: the law of K written out; d, m ≤ N only excludes undefined parameters
-- source:
--   Hwang, Jaillet, Manshadi, Online Resource Allocation under Partially Predictable Demand, arXiv:1810.00447v1, Theorem EC.2, p.ec2 (PDF 39)

import Mathlib
import Definitions.Def_PartPredAlloc_hyperPMF

namespace PartPredAlloc

/-- **Theorem EC.2 (Hush and Scovel 2005)** (Hwang–Jaillet–Manshadi, arXiv:1810.00447v1,
Theorem EC.2, p.ec2 = PDF 39; cited from D. Hush, C. Scovel, *Concentration of the hypergeometric
distribution*, Statistics & Probability Letters 75(2) (2005) 127–132). Let `K ∼ Hyper(n₁, n, m)`
count the defectives selected when `n₁` items are drawn without replacement from a population of
`n` items of which `m` are defective, and let `γ ≥ 2`. Then
`P(K − E[K] > γ) < e^{−2α(γ² − 1)}` and `P(K − E[K] < −γ) < e^{−2α(γ² − 1)}`, where
`α = max{1/(n₁ + 1) + 1/(n − n₁ + 1), 1/(m + 1) + 1/(n − m + 1)}`.

**Formalization Note.** Population `n` is `N`, draws `n₁` are `d`, defectives `m` are `m`
(`d, m ≤ N`). `E[K] = d m / N`. The probabilities are sums of `hyperPMF N d m k` over the possible
values `k ∈ {0, …, min(d, m)}` in the event. -/
theorem theorem_EC_2 (N d m : ℕ) (hd : d ≤ N) (hm : m ≤ N) (γ : ℝ) (hγ : 2 ≤ γ) :
    (∑ k ∈ (Finset.range (min d m + 1)).filter
        (fun k : ℕ => γ < (k : ℝ) - (d : ℝ) * m / N), hyperPMF N d m k) <
      Real.exp (-2 * max (1 / ((d : ℝ) + 1) + 1 / ((N : ℝ) - d + 1))
        (1 / ((m : ℝ) + 1) + 1 / ((N : ℝ) - m + 1)) * (γ ^ 2 - 1)) ∧
    (∑ k ∈ (Finset.range (min d m + 1)).filter
        (fun k : ℕ => (k : ℝ) - (d : ℝ) * m / N < -γ), hyperPMF N d m k) <
      Real.exp (-2 * max (1 / ((d : ℝ) + 1) + 1 / ((N : ℝ) - d + 1))
        (1 / ((m : ℝ) + 1) + 1 / ((N : ℝ) - m + 1)) * (γ ^ 2 - 1)) := by sorry

end PartPredAlloc
