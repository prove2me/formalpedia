-- Prove2me | Theorems.Thm_ReusableMatching_theorem_1
-- name    : ReusableMatching.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:33:47.889627+00:00
-- url     : https://prove2.me/theorems/a9be1959-5ef1-4268-a67d-89d383445808
-- title:
--   Theorem 1: Periodic Reranking with $\beta=0.89$ is $0.5893$-competitive for vertex-weighted OBMRR
-- statement:
--   Let an instance of vertex-weighted online bipartite matching with reusable resources be given: a finite set $V$ of resources (with any fixed priority order), $n$ arrivals, edges $E$, weights $r_i\ge0$ and a usage duration $d\ge1$. Run Periodic Reranking (Algorithm 1) with $\beta=0.89$ on independent seeds, uniform on $[0,1]$, redrawn every $d$ arrivals. Then:
--
--   1. for every seed vector, the output of Periodic Reranking is a feasible reusable matching;
--   2. Periodic Reranking is online: its decisions at the arrivals $0,\dots,j$ depend only on the edges of those arrivals, on the seeds of the periods up to the period of $j$, and on the weights and the duration;
--   3. its expected reward is at least $0.5893$ times the optimal offline reward:
--   $$
--   \mathbb E_Y\Bigl[\sum_{(i,t)\in\mathrm{PR}(Y)} r_i\Bigr]\ \ge\ 0.5893\cdot\mathrm{OPT}.
--   $$
--
--   This was the first integral online algorithm shown to beat the greedy ratio $1/2$ for this problem.
--
--   Differences from the source:
--   - reading: competitive ratio Γ ≈ 0.589 → Γ = 0.5893; reason: the proof establishes 0.5893 ("Now we show our constructed dual satisfies Lemma 1 for Γ ≈ 0.5893", p.8; "both terms are greater than 0.5893", p.13), the stronger reading of ≈ 0.589
--   - reading: "achieves a competitive ratio of Γ" for an online algorithm (p.2) → three clauses: a feasible reusable matching for every seed vector, online decisions (dependence only on past edges, seeds of past and current periods, r and d), and E[reward] ≥ Γ · OPT on every instance; reason: formal content of "online algorithm", of arrivals that "reveal their incident edges … upon arrival" (p.2), of seeds generated "every d time units" (p.8), and of Γ-competitive (p.2)
--   - reading: arg max over the available neighbours, no tie rule (Algorithm 1, p.8) → the least maximizer for a linear order on V (a fixed priority order; V and its order are arbitrary); reason: the paper fixes no tie rule; its proofs of Lemmas 4, 6 and 8 compare runs at fixed seeds and need a choice among tied resources that does not depend on the seeds
--   - encoding: arrivals 1, …, |U|; periods of length d with a dummy period before the first arrival (p.8) → arrivals Fin n numbered from 0; arrival t lies in period t / d + 1; period 0 is the dummy period; seeds indexed by V × Fin (n + 1); reason: Lean convention; same instances and same runs
--   - encoding: d ∈ ℕ (p.2) → 1 ≤ d, as a field of the instance; reason: the model ("unavailable for the next d − 1 periods") has no meaning at d = 0
--   - encoding: E_Y[·] over i.i.d. U[0,1] seeds → Bochner integral with respect to seedMeasure, the product of the uniform measures on unitInterval; reason: Lean convention; the integrands are bounded
-- source:
--   Delong, Farhadi, Niazadeh, Sivan & Udwani, Online Bipartite Matching with Reusable Resources, arXiv:2110.07084v2, Theorem 1, p.4 (proof p.13; "Γ ≈ 0.5893", p.8)

import Mathlib
import Definitions.Def_ReusableMatching_OPT
import Definitions.Def_ReusableMatching_matchedPairs
import Definitions.Def_ReusableMatching_reward

namespace ReusableMatching

open MeasureTheory

/-- **Theorem 1 (Main Result I)** of Delong, Farhadi, Niazadeh, Sivan & Udwani, *Online Bipartite
Matching with Reusable Resources*, arXiv:2110.07084v2, p.4 (proof p.13): "The Periodic Reranking
algorithm (Algorithm 1 with `β = 0.89`), achieves a competitive ratio of `Γ ≈ 0.589` in the
(vertex-weighted) OBMRR problem."

For every instance (finite resources `V` with any priority order, `n` arrivals, edges `E`, weights
`r ≥ 0`, usage duration `d ≥ 1`), Periodic Reranking with `β = 0.89`:
1. outputs, for every seed vector `Y`, a feasible reusable matching of the instance;
2. is online: its decisions at the arrivals `0, …, j` depend only on the edges of those arrivals
   and on the seeds of the periods up to the period of `j` (the weights `r` and the duration `d`
   are known in advance);
3. earns, in expectation over the i.i.d. uniform seeds, at least `0.5893 · OPT`, where `OPT` is the
   optimal offline reward.

**Formalization Note.**
* The constant is `0.5893`: the paper's proof establishes it ("Now we show our constructed dual
  satisfies Lemma 1 for `Γ ≈ 0.5893`", p.8; "both terms are greater than `0.5893`, giving us the
  desired guarantee", p.13), and it is stronger than the `≈ 0.589` printed in the theorem.
* "Online" (p.2: arrivals "reveal their incident edges to vertices in `V` upon arrival"; p.8: new
  seeds "Every `d` time units") is clause 2: two instances with the same `r` and `d` whose edges
  agree on the arrivals `≤ j`, and two seed vectors that agree on the periods `≤ k(j)`, give the
  same decisions at all arrivals `t ≤ j`.
* The expectation is the Bochner integral with respect to `seedMeasure`. -/
theorem theorem_1 {V : Type*} [Fintype V] [LinearOrder V] {n : ℕ} (I : OBMRRInstance V n) :
    (∀ Y : Seeds V n, IsFeasibleMatching I (matchedPairs I (89 / 100) Y)) ∧
    (∀ I' : OBMRRInstance V n, I'.r = I.r → I'.d = I.d →
      ∀ (Y Y' : Seeds V n) (j : Fin n),
        (∀ p : V × Fin n, p.2 ≤ j → (p ∈ I.E ↔ p ∈ I'.E)) →
        (∀ (v : V) (k : Fin (n + 1)), k ≤ period I j → Y (v, k) = Y' (v, k)) →
        ∀ t : Fin n, t ≤ j →
          PeriodicReranking I (89 / 100) Y t = PeriodicReranking I' (89 / 100) Y' t) ∧
    (5893 / 10000 : ℝ) * OPT I ≤ ∫ Y, reward I (89 / 100) Y ∂(seedMeasure V n) := by sorry

end ReusableMatching
