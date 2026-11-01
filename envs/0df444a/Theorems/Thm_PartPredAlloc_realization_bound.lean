-- Prove2me | Theorems.Thm_PartPredAlloc_realization_bound
-- name    : PartPredAlloc.realization_bound
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:19:02.45189+00:00
-- url     : https://prove2.me/theorems/eadb81f9-8f5e-4f14-b372-9882919a385a
-- title:
--   Proof of Theorem 1, display after (5), p.16 — every realization in $\mathcal E$ has $ALG_1/OPT\ge p+\frac{1-p}{2-a}-O(\epsilon)$
-- statement:
--   Let $\theta=\frac{1-p}{2-a}$ and $\epsilon=\frac1{a(1-p)p}\sqrt{\frac{\log n}b}$. There is a constant $K$ such that for all $n\ge3$, $1\le b\le n$, $a,p\in(0,1)$ satisfying (5), $b>\frac1{\bar\epsilon^2}\frac{\log n}{a^2(1-p)^2p^2}$ with $\bar\epsilon=1/24$, every adversarial sequence $\vec v_I$ and every realization $\vec v$ belonging to the event $\mathcal E$,
--
--   $$
--   \frac{ALG_1(\vec v)}{OPT(\vec v_I)}\ge p+\frac{1-p}{2-a}-K\epsilon .
--   $$
--
--   This is the realization-wise core of the proof of Theorem 1; combined with Lemma 1 ($\Pr(\mathcal E)\ge1-\epsilon$) it gives the theorem.
--
--   Differences from the source:
--   - reading: Lemma 8 / the display after (5) printed without hypotheses → assumption (5): b > (1/ε̄²) log n / (a²(1−p)²p²); reason: both sit inside the proof of Theorem 1 after "without loss of generality, we assume (5)" (p.16), and their proofs use it; without (5), Lemma 8(c) is false (its ratio to ε is k(1−p)√(log n / b)/p, unbounded as p → 0 at n = 3, b = 1)
--   - encoding: O(ε) (Definition 2: ∃ k, f(x) < k g(x) for all x) → ∃ K, chosen before n, b, a, p (and the instance), with the bound for all of them; reason: Definition 2 quantifies one constant over the whole domain
--   - encoding: "under event E", the realization v → every outcome (S, σ) with σ ∈ fixers S and EventE p vI S σ, v = arrival vI σ; reason: the realizations of the model are exactly these outcomes
--   - encoding: ALG₁(v)/OPT(v_I) ≥ c → c · OPT(v_I) ≤ ALG₁(v); reason: equivalent when OPT(v_I) > 0; when OPT(v_I) = 0 the ratio is undefined and the product form holds trivially since ALG₁ ≥ 0
--   - encoding: b units (b ≥ 0) → 1 ≤ b; reason: ε = √(log n / b)/(a(1−p)p) and (5) are undefined at b = 0
-- source:
--   Hwang, Jaillet, Manshadi, Online Resource Allocation under Partially Predictable Demand, arXiv:1810.00447v1, proof of Theorem 1, display after (5), p.16

import Mathlib
import Definitions.Def_PartPredAlloc_EventE
import Definitions.Def_PartPredAlloc_alg1

namespace PartPredAlloc

/-- **Realization-wise bound** (Hwang–Jaillet–Manshadi, arXiv:1810.00447v1, proof of Theorem 1,
display after (5), p.16): under (5), for any realization `v` belonging to event `𝓔`,
`ALG₁(v)/OPT(v_I) ≥ p + (1 − p)/(2 − a) − O(ε)`, with `ε = (1/(a(1 − p)p)) √(log n / b)`.

**Formalization Note.** `O(ε)` is Definition 2 (p.12): one constant `K`, chosen before
`n, b, a, p, v_I` and the outcome. The ratio is written multiplicatively. Realizations are the
outcomes `(S, σ)` with `σ ∈ fixers S`, `v = v_I ∘ σ⁻¹`. The domain is `n ≥ 3`, `1 ≤ b ≤ n`,
`a, p ∈ (0, 1)` with the standing assumption (5): `b > (1/ε̄²) log n / (a²(1 − p)²p²)`. -/
theorem realization_bound :
    ∃ K : ℝ, ∀ (n b : ℕ) (a p : ℝ), 3 ≤ n → 1 ≤ b → b ≤ n → 0 < a → a < 1 → 0 < p → p < 1 →
      (b : ℝ) > 1 / epsBar ^ 2 * (Real.log n / (a ^ 2 * (1 - p) ^ 2 * p ^ 2)) →
      ∀ (vI : Fin n → Cust) (S : Finset (Fin n)) (σ : Equiv.Perm (Fin n)), σ ∈ fixers S →
        EventE p vI S σ →
        (p + theta a p - K * epsErr n b a p) * OPT b a vI ≤ alg1 n b a p (arrival vI σ) := by sorry

end PartPredAlloc
