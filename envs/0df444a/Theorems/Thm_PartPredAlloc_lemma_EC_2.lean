-- Prove2me | Theorems.Thm_PartPredAlloc_lemma_EC_2
-- name    : PartPredAlloc.lemma_EC_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:18:06.292561+00:00
-- url     : https://prove2.me/theorems/68f483a0-2a22-41a4-8834-c8676f61b903
-- title:
--   Lemma EC.2, p.ec4 — $R$, $R_1$, $Z$ lie in their windows with probability $\ge1-\epsilon/4$ (corrected: $n_1\ge1$)
-- statement:
--   Let $n\ge3$, $p\in(0,1)$, let $\vec v_I$ contain $n_1\ge1$ type-1 customers, let $\lambda=t/n$ with $t\in\{1,\dots,n\}$ and $\epsilon\in(0,1/24]$. Then with probability at least $1-\epsilon/4$ over the stochastic group, all three events (EC.1a)–(EC.1c) happen:
--
--   $$
--   R\in\Big(np-\sqrt{n\log\tfrac1\epsilon},\,np+\sqrt{n\log\tfrac1\epsilon}\Big),\quad
--   R_1\in\Big(n_1p-\sqrt{n_1\log\tfrac1\epsilon},\,n_1p+\sqrt{n_1\log\tfrac1\epsilon}\Big),\quad
--   Z\in\Big(\lambda np-\sqrt{\lambda n\log\tfrac1\epsilon},\,\lambda np+\sqrt{\lambda n\log\tfrac1\epsilon}\Big).
--   $$
--
--   Here $\bar\epsilon_{EC.2}=1/24$ and $\alpha_{EC.2}=1$. Since $R\sim\mathrm{Bin}(n,p)$, $R_1\sim\mathrm{Bin}(n_1,p)$ and $Z\sim\mathrm{Bin}(\lambda n,p)$, this is the first step of the concentration of $O_1(\lambda)$.
--
--   Differences from the source:
--   - correction: for every instance → n₁ ≥ 1 (nType1 vI ≥ 1); reason: false at n₁ = 0: for v_I = (0, 0, 0), (EC.1b) asks R₁ = 0 ∈ (0, 0), so the probability is 0 < 1 − ε/4; the only use (Lemma EC.1, n₁ > (4/p²) log(1/ε′) > 0) supplies n₁ ≥ 1
--   - encoding: probability over the stochastic group S and the random permutation σ_S → prob n p: explicit finite sum with weights p^{|S|}(1−p)^{n−|S|} and σ uniform over the permutations fixing every position outside S; reason: the model has finitely many outcomes; this is its law (§3, p.10), with no measure theory
--   - encoding: λ ∈ {1/n, 2/n, …, 1} → t : ℕ with 1 ≤ t ≤ n and λ = t/n; reason: same set of times
-- source:
--   Hwang, Jaillet, Manshadi, Online Resource Allocation under Partially Predictable Demand, arXiv:1810.00447v1, Lemma EC.2, p.ec4 (PDF 41)

import Mathlib
import Definitions.Def_PartPredAlloc_EventEC1

namespace PartPredAlloc

/-- **Lemma EC.2** (Hwang–Jaillet–Manshadi, arXiv:1810.00447v1, Lemma EC.2, p.ec4 = PDF 41),
corrected with `n₁ ≥ 1`. Let `ε̄_{EC.2} = 1/24` and `α_{EC.2} = 1`. For `ε ∈ (0, 1/24]` and
`λ = t/n ∈ {1/n, …, 1}`, with probability at least `1 − ε/4` the events (EC.1a)–(EC.1c) all happen:
`R`, `R₁` and `Z` lie in their open windows of half-width `√(m log(1/ε))` (`m = n, n₁, λn`) around
`np`, `n₁p`, `λnp` (`EventEC1`).

**Formalization Note.** The probability is over the outcome `(S, σ)` of the partially predictable
model; the event depends on `S` only. Standing assumptions of the model (§3, pp.9–10): `n ≥ 3`,
`p ∈ (0, 1)`. Correction: with `n₁ = 0`, (EC.1b) asks `R₁ = 0 ∈ (0, 0)`, so the printed statement
is false; `n₁ ≥ 1` is added, which is what its only use (Lemma EC.1, `n₁ > (4/p²) log(1/ε′) > 0`)
supplies. -/
theorem lemma_EC_2 {n : ℕ} (hn : 3 ≤ n) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (vI : Fin n → Cust) (hn1 : 1 ≤ nType1 vI) (t : ℕ) (ht1 : 1 ≤ t) (htn : t ≤ n)
    (ε : ℝ) (hε0 : 0 < ε) (hε : ε ≤ 1 / 24) :
    1 - ε / 4 ≤ prob n p (fun S _ => EventEC1 p ε vI S t) := by sorry

end PartPredAlloc
