-- Prove2me | Theorems.Thm_PartPredAlloc_lemma_3
-- name    : PartPredAlloc.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:19:09.622544+00:00
-- url     : https://prove2.me/theorems/a26802f8-6398-4082-b37a-b8374d608bde
-- title:
--   Lemma 3, p.17 — on $\mathcal E$ with exhausted inventory, $ALG_1/OPT\ge p+\frac{1-p}{2-a}-\frac{(1-a)\Delta}{ab}$
-- statement:
--   Let $n\ge3$, $1\le b\le n$, $a,p\in(0,1)$, $k=16$ and $\Delta=\alpha\sqrt{b\log n}$. Under event $\mathcal E$, if $n_1\ge\frac k{p^2}\log n$ and Algorithm 1 exhausts the inventory, $q_1(1)+q_{2,e}(1)+q_{2,f}(1)=b$, then
--
--   $$
--   \frac{ALG_1(\vec v)}{OPT(\vec v)}\ge p+\frac{1-p}{2-a}-\frac{(1-a)\Delta}{ab}.
--   $$
--
--   This is the competitive bound of Case (i) of the proof of Theorem 1.
--
--   Differences from the source:
--   - encoding: "under event E", the realization v → every outcome (S, σ) with σ ∈ fixers S and EventE p vI S σ, v = arrival vI σ; reason: the realizations of the model are exactly these outcomes
--   - encoding: ALG₁(v)/OPT(v) ≥ c → (p + θ − (1−a)∆/(ab)) · OPT(v_I) ≤ ALG₁(v); reason: OPT(v) = OPT(v_I) (p.11) and OPT > 0 under the hypotheses (n₁ ≥ (16/p²) log n > 0, b ≥ 1), so the two forms are equivalent
--   - encoding: b units (b ≥ 0) → 1 ≤ b; reason: the printed (1−a)∆/(ab) is undefined at b = 0; the paper's b units presuppose b ≥ 1
-- source:
--   Hwang, Jaillet, Manshadi, Online Resource Allocation under Partially Predictable Demand, arXiv:1810.00447v1, Lemma 3, p.17; proof p.ec12 (PDF 49)

import Mathlib
import Definitions.Def_PartPredAlloc_EventE
import Definitions.Def_PartPredAlloc_alg1

namespace PartPredAlloc

/-- **Lemma 3** (Hwang–Jaillet–Manshadi, arXiv:1810.00447v1, Lemma 3, p.17; proof p.ec12). Under
event `𝓔`, if `n₁ ≥ (k/p²) log n` and `q₁(1) + q₂,ₑ(1) + q₂,f(1) = b`, then
`ALG₁(v)/OPT(v) ≥ p + (1 − p)/(2 − a) − (1 − a)∆/(ab)`.

**Formalization Note.** The ratio is written multiplicatively,
`ALG₁(v) ≥ (p + θ − (1 − a)∆/(ab)) · OPT(v_I)`; `OPT(v) = OPT(v_I)` (p.11) and `OPT > 0` under the
hypotheses. For every outcome `(S, σ)` (`σ ∈ fixers S`) in `𝓔`, `v = v_I ∘ σ⁻¹`. Standing
assumptions: `n ≥ 3`, `1 ≤ b ≤ n`, `a ∈ (0, 1)`, `p ∈ (0, 1)`. -/
theorem lemma_3 {n : ℕ} (hn : 3 ≤ n) (b : ℕ) (hb1 : 1 ≤ b) (hbn : b ≤ n)
    (a p : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (hp0 : 0 < p) (hp1 : p < 1)
    (vI : Fin n → Cust) (S : Finset (Fin n)) (σ : Equiv.Perm (Fin n)) (hσ : σ ∈ fixers S)
    (hE : EventE p vI S σ) (hn1 : (nType1 vI : ℝ) ≥ kL1 / p ^ 2 * Real.log n)
    (hfull : q1F n b a p (arrival vI σ) + q2eF n b a p (arrival vI σ) +
      q2fF n b a p (arrival vI σ) = b) :
    (p + theta a p - (1 - a) * Delta n b / (a * b)) * OPT b a vI ≤
      alg1 n b a p (arrival vI σ) := by sorry

end PartPredAlloc
