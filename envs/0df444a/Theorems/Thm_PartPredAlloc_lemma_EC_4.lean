-- Prove2me | Theorems.Thm_PartPredAlloc_lemma_EC_4
-- name    : PartPredAlloc.lemma_EC_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:18:18.436193+00:00
-- url     : https://prove2.me/theorems/a892b0f7-6efa-4b06-b628-1be243f19a95
-- title:
--   Lemma EC.4, p.ec5 — conditional concentration of $Z_1$ around $ZR_1/R$
-- statement:
--   Let $n\ge3$, $p\in(0,1)$, $\lambda=t/n$ with $t\in\{1,\dots,n\}$, $\epsilon\in(0,1/24]$ and $n_1>\frac4{p^2}\log\frac1\epsilon$. For every stochastic group $\mathcal S$ on which (EC.1a)–(EC.1c) hold, under the uniform random permutation of $\mathcal S$,
--
--   $$
--   \Pr\Big(\Big|Z_1-\frac{ZR_1}{R}\Big|\ge\sqrt6\sqrt{n_1\log\tfrac1\epsilon}\ \Big|\ \mathcal S\Big)\le\frac\epsilon4 .
--   $$
--
--   Here $\bar\epsilon_{EC.4}=1/24$, $\alpha_{EC.4}=\sqrt6$, $k_{EC.4}=4$, and $ZR_1/R=\mathbb E[Z_1\mid R,R_1,Z]$ by (EC.2). Given $\mathcal S$, $Z_1$ is hypergeometric: $Z$ draws from the $R$ stochastic customers, $R_1$ of which are type-1.
--
--   Differences from the source:
--   - generalization: P(· | R, R₁, Z) for (R, R₁, Z) ∈ E → probGivenS S (conditioning on the stochastic group S) for every S satisfying EventEC1; reason: S determines (R, R₁, Z); averaging the S-conditional bound over the S with given (R, R₁, Z) gives the printed bound
--   - encoding: E[Z₁ | R, R₁, Z] → Z R₁ / R; reason: the paper's own (EC.2)
--   - encoding: λ ∈ {1/n, 2/n, …, 1} → t : ℕ with 1 ≤ t ≤ n and λ = t/n; reason: same set of times
-- source:
--   Hwang, Jaillet, Manshadi, Online Resource Allocation under Partially Predictable Demand, arXiv:1810.00447v1, Lemma EC.4, p.ec5 (PDF 42)

import Mathlib
import Definitions.Def_PartPredAlloc_EventEC1

namespace PartPredAlloc

/-- **Lemma EC.4** (Hwang–Jaillet–Manshadi, arXiv:1810.00447v1, Lemma EC.4, p.ec5 = PDF 42). Let
`ε̄_{EC.4} = 1/24`, `α_{EC.4} = √6` and `k_{EC.4} = 4`. For `ε ∈ (0, 1/24]`, if
`n₁ > (4/p²) log(1/ε)` and `(R, R₁, Z)` satisfy (EC.1a)–(EC.1c), then
`P(|Z₁ − E[Z₁ | R, R₁, Z]| ≥ √6 √(n₁ log(1/ε)) | R, R₁, Z) ≤ ε/4`.

**Formalization Note.** The conditioning is on the stochastic group `S` (which determines
`R, R₁, Z`), with `σ` uniform over the permutations fixing the complement of `S`
(`probGivenS`); averaging over the `S` with given `(R, R₁, Z)` gives the printed bound. The
conditional mean is written `Z R₁ / R`, the paper's (EC.2). `λ = t/n`, `t ∈ {1, …, n}`. Standing
assumptions: `n ≥ 3`, `p ∈ (0, 1)`. -/
theorem lemma_EC_4 {n : ℕ} (hn : 3 ≤ n) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (vI : Fin n → Cust) (t : ℕ) (ht1 : 1 ≤ t) (htn : t ≤ n)
    (ε : ℝ) (hε0 : 0 < ε) (hε : ε ≤ 1 / 24)
    (hn1 : (nType1 vI : ℝ) > 4 / p ^ 2 * Real.log (1 / ε))
    (S : Finset (Fin n)) (hS : EventEC1 p ε vI S t) :
    probGivenS S (fun σ => Real.sqrt 6 * Real.sqrt ((nType1 vI : ℝ) * Real.log (1 / ε)) ≤
        |(ecZ1 vI S σ t : ℝ) - (ecZ S t : ℝ) * ecR1 vI S / ecR S|) ≤ ε / 4 := by sorry

end PartPredAlloc
