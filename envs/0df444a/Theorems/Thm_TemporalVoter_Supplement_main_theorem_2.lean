-- Prove2me | Theorems.Thm_TemporalVoter_Supplement_main_theorem_2
-- name    : TemporalVoter.Supplement.main_theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T23:32:49.548305+00:00
-- url     : https://prove2.me/theorems/b2162b8a-c60a-4af4-a4cf-1c701cc797cc
-- title:
--   Main Theorem 2 — the voter model on some 3-regular temporal graphs does not reach consensus within $cn/\Phi(\mathcal G)$ with probability at least $1/2$
-- statement:
--   This is the lower bound matching Main Theorem 1 in its dependence on the temporal conductance $\Phi(\mathcal G)$.
--
--   For a temporal graph $\mathcal G$ with fixed degrees, let $\Phi(\mathcal G)$ be its temporal conductance, and run the standard voter model $(\xi_t)_{t\ge0}$ on $\mathcal G$: at each step every vertex, independently, with probability $1/2$ copies the opinion of a uniformly random neighbour in the current graph $G_t$ and otherwise keeps its own. The voter model **absorbs** at the first time all vertices hold the same opinion.
--
--   **Theorem.** There is a constant $c>0$ such that for every $N$ there are $n\ge N$ and a $3$-regular temporal graph $\mathcal G$ on $n$ vertices with $\Phi(\mathcal G)>0$, together with an initial state $\xi_0$ using two opinions, such that
--   $$
--   \mathbb P\Bigl(\text{no } t\le \frac{c\,n}{\Phi(\mathcal G)} \text{ has } \xi_t \text{ constant}\Bigr)\;\ge\;\frac12 .
--   $$
--
--   Together with Main Theorem 1 (whose bound for $3$-regular graphs is $O(m/\Phi(\mathcal G))=O(n/\Phi(\mathcal G))$), this shows that the dependence on $\Phi(\mathcal G)$ cannot be improved in general.
--
--   **Formalization Note** The constant $c$ is chosen before the graphs. The vertex set is $\{0,\dots,n-1\}$. "Does not absorb within time $X$" is the event that no time $t\le X$ is a consensus. $\Phi(\mathcal G)>0$ is part of the conclusion, so that $cn/\Phi(\mathcal G)$ is finite as in the paper.
--
--   Differences from the source:
--   - reading: "constant c" next to "arbitrarily large … graphs" → c > 0 chosen before N and the graphs; reason: if c could depend on the graph the statement would be trivial; the proof's c is absolute
--   - encoding: cn/Φ(𝒢) with Φ(𝒢) finite and positive in the paper's construction → 0 < Φ(𝒢) as part of the conclusion; reason: Lean's x/0 = 0 would otherwise turn the bound into time 0; the paper's graphs have Φ ≥ φ(n)/Δ(n) > 0
--   - reading: "from some initial state" → an initial state with two opinions (Fin 2); reason: the paper's construction starts from a minority set (two opinions); the Lean statement implies the one with an unspecified number of opinions
--   - encoding: "arbitrarily large n-vertex" → ∀ N, ∃ n ≥ N, a graph on Fin n; reason: Lean convention, same instances
-- source:
--   Rocha Avila, Dell, Lapinskas, Temporal Conductance and Bounds on the Voter Model for Dynamic Networks, arXiv:2606.13374 (2 Nov 2026), Main Theorem 2, p.7 (restated with proof p.33)

import Mathlib
import Definitions.Def_TemporalVoter_voterLaw
import Definitions.Def_TemporalVoter_temporalConductance

open scoped ENNReal

namespace TemporalVoter

namespace Supplement

/-- **Main Theorem 2 (Lower bound)** (Rocha Avila, Dell, Lapinskas, *Temporal Conductance and
Bounds on the Voter Model for Dynamic Networks*, arXiv:2606.13374, version of 2 Nov 2026, p.7,
restated p.33): there are a constant `c > 0` and arbitrarily large `n`-vertex 3-regular temporal
graphs `G` such that, from some initial state, with probability at least `1/2` the standard voter
model on `G` does not absorb within time `cn/Φ(G)`.

**Formalization Note** The constant `c` is chosen before the graphs (uniform); "arbitrarily
large" is `∀ N, ∃ n ≥ N`; the vertex set is `Fin n`. `Φ(G) > 0` is part of the conclusion, so
that `cn/Φ(G)` is the paper's finite time and not Lean's `x / 0 = 0`. The initial state is a
two-opinion state (the paper's construction starts from a minority set, p.32). "Does not absorb
within time `X`" is: no time `t ≤ X` is a consensus, i.e. the consensus time exceeds `X`. -/
theorem main_theorem_2 : ∃ c : ℝ, 0 < c ∧
    ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ ∃ T : TemporalGraph (Fin n),
      (∀ v, T.d v = 3) ∧ 0 < temporalConductance T ∧
      ∃ σ₀ : Fin n → Fin 2, (1 / 2 : ℝ≥0∞) ≤ voterLaw T 2 σ₀
        {ω | ∀ t : ℕ, (t : ℝ) ≤ c * n / temporalConductance T → ¬ IsConsensus (ω t)} := by sorry

end Supplement

end TemporalVoter
