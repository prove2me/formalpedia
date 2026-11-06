-- Prove2me | Theorems.Thm_TemporalVoter_main_theorem_1
-- name    : TemporalVoter.main_theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:12:07.919645+00:00
-- url     : https://prove2.me/theorems/3d10127f-f63c-4d11-a941-fb706a48e2d4
-- title:
--   Main Theorem 1 — with probability at least $1/2$ the voter model reaches consensus within $b'm/(d_{\min}\Phi(\mathcal G))$ steps
-- statement:
--   There is a constant $b'>0$ such that the following holds. Consider the standard voter model, with any number of opinions, on an $n$-vertex temporal graph $\mathcal G$ with fixed vertex degrees, $m$ edges and minimum degree $d_{\min}$, with arbitrary initial state. Then with probability at least $1/2$ the consensus time is at most
--   $$\frac{b'\,m}{d_{\min}\,\Phi(\mathcal G)},$$
--   where $\Phi(\mathcal G)=\max_{\Delta\ge1}\phi^\Delta(\mathcal G)/\Delta$ is the temporal conductance.
--
--   The constant $b'$ is absolute: it is chosen before the vertex set, the graph sequence, the number of opinions and the initial state. On a static graph $\Phi(\mathcal G)$ is the ordinary conductance and the bound is the known $O(m/(d_{\min}\phi))$ bound; on a dynamic network it remains finite even when every snapshot is disconnected.
--
--   Differences from the source:
--   - encoding: the voter process (ξ_t : t ≥ 0) of Definition 1.2 on some probability space → the path measure voterLaw on ℕ → (V → Fin k), built by Ionescu-Tulcea (Kernel.traj) from the synchronous lazy step kernels of Definition 1.2, started at σ₀; reason: the process is constructed from its definition (paper.md R4); every event and expectation of the paper is one of this law
--   - encoding: the consensus time is at most x → the event ∃ t ≤ x with ξ_t constant; reason: the consensus time is the first t with ξ_t constant (Definition 1.2), so this is the same event (paper.md R2)
--   - encoding: the bound b′m/(d_min Φ(G)) for every temporal graph with fixed degrees → the hypothesis 0 < Φ(G); reason: for Φ(G) = 0 the bound is b′m/0, undefined (infinite, vacuous) in the paper, while Lean's x/0 = 0 would assert consensus at time 0; the hypothesis excludes exactly that case (paper.md R1)
--   - encoding: κ a positive integer, σ₀ : V → {0, …, κ − 1} → k : ℕ and σ₀ : V → Fin k; reason: k = 0 admits a state only when V is empty, which 0 < Φ(G) excludes
--   - encoding: an n-vertex vertex set → a Fintype V; reason: same; n = |V|
--   - encoding: a sequence of undirected graphs on a common vertex set V(G) with common degree d(v) → T : TemporalGraph V: a Fintype V, G t : SimpleGraph V, and the degree data d with degree_eq and one_le_d; reason: the paper's graphs are plain finite graphs (n vertices, m = ½ ∑ d(v) edges, e_t counts edges); no loop or parallel edge occurs in them, the self-loop of Figure 1 only pictures laziness
-- source:
--   Rocha Avila, Dell, Lapinskas, Temporal Conductance and Bounds on the Voter Model for Dynamic Networks, arXiv:2606.13374 (2 Nov 2026), Main Theorem 1, p.7 (restated with proof p.28)

import Mathlib
import Definitions.Def_TemporalVoter_voterLaw
import Definitions.Def_TemporalVoter_temporalConductance

open scoped ENNReal

namespace TemporalVoter

/-- **Main Theorem 1 (Upper bound)** (Rocha Avila, Dell, Lapinskas, *Temporal Conductance and Bounds
on the Voter Model for Dynamic Networks*, arXiv:2606.13374, version of 2 Nov 2026, p.7, restated
p.28): there is a constant `b' > 0` such that, for the standard voter model on any `n`-vertex
temporal graph `G` with fixed vertex degrees, `m` edges and minimum degree `d_min`, with any number
`k` of opinions and arbitrary initial state `σ₀`, with probability at least `1/2` the consensus time
is at most `b'm/(d_min Φ(G))`.

**Formalization Note** `0 < Φ(G)` is assumed: for `Φ(G) = 0` the bound `b'm/(d_min · 0)` is
undefined in the paper (infinite) while Lean's `x / 0 = 0` would make it time `0`. The constant
`b'` is chosen before the vertex type, the graph, `k` and `σ₀`. "The consensus time is at most
`x`" is the event that some time `t ≤ x` has all opinions equal. -/
theorem main_theorem_1 : ∃ b' : ℝ, 0 < b' ∧
    ∀ (V : Type) [Fintype V] (T : TemporalGraph V), 0 < temporalConductance T →
      ∀ (k : ℕ) (σ₀ : V → Fin k), (1 / 2 : ℝ≥0∞) ≤ voterLaw T k σ₀
        {ω | ∃ t : ℕ, (t : ℝ) ≤ b' * T.m / (T.dmin * temporalConductance T) ∧
          IsConsensus (ω t)} := by sorry

end TemporalVoter
