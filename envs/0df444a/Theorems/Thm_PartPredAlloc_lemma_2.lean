-- Prove2me | Theorems.Thm_PartPredAlloc_lemma_2
-- name    : PartPredAlloc.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:19:08.19689+00:00
-- url     : https://prove2.me/theorems/95ec0780-7fc0-4a0e-9f98-cfb0954c6b38
-- title:
--   Lemma 2, p.17 — on $\mathcal E$, $q_{2,e}(1)\le p(b-n_1)^++\Delta$
-- statement:
--   Let $n\ge3$, $b\le n$, $a,p\in(0,1)$, and let $k=16$, $\Delta=\alpha\sqrt{b\log n}$ with $\alpha=10+2\sqrt6$. Under event $\mathcal E$, if $n_1\ge\frac k{p^2}\log n$, then the number of type-2 customers accepted by the evolving threshold rule of Algorithm 1 satisfies
--
--   $$
--   q_{2,e}(1)\le p(b-n_1)^++\Delta .
--   $$
--
--   This controls the loss from accepting too many type-2 customers when the inventory runs out.
--
--   Differences from the source:
--   - encoding: "under event E", the realization v → every outcome (S, σ) with σ ∈ fixers S and EventE p vI S σ, v = arrival vI σ; reason: the realizations of the model are exactly these outcomes
-- source:
--   Hwang, Jaillet, Manshadi, Online Resource Allocation under Partially Predictable Demand, arXiv:1810.00447v1, Lemma 2, p.17

import Mathlib
import Definitions.Def_PartPredAlloc_EventE
import Definitions.Def_PartPredAlloc_alg1

namespace PartPredAlloc

/-- **Lemma 2** (Hwang–Jaillet–Manshadi, arXiv:1810.00447v1, Lemma 2, p.17). Under event `𝓔`, if
`n₁ ≥ (k/p²) log n`, then `q₂,ₑ(1) ≤ p (b − n₁)⁺ + ∆`, with `k = 16` and `∆ = α √(b log n)`.

**Formalization Note.** For every outcome `(S, σ)` of the model (`σ ∈ fixers S`) in the event `𝓔`
(`EventE`), Algorithm 1 is run on the realized sequence `v = v_I ∘ σ⁻¹`. Standing assumptions
(§3, pp.9–10): `n ≥ 3`, `b ≤ n`, `a ∈ (0, 1)`, `p ∈ (0, 1)`; `b = 0` is allowed, as on the page
(the bound is defined there). -/
theorem lemma_2 {n : ℕ} (hn : 3 ≤ n) (b : ℕ) (hbn : b ≤ n)
    (a p : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (hp0 : 0 < p) (hp1 : p < 1)
    (vI : Fin n → Cust) (S : Finset (Fin n)) (σ : Equiv.Perm (Fin n)) (hσ : σ ∈ fixers S)
    (hE : EventE p vI S σ) (hn1 : (nType1 vI : ℝ) ≥ kL1 / p ^ 2 * Real.log n) :
    (q2eF n b a p (arrival vI σ) : ℝ) ≤ p * max ((b : ℝ) - nType1 vI) 0 + Delta n b := by sorry

end PartPredAlloc
