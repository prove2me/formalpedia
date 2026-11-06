-- Prove2me | Theorems.Thm_TemporalVoter_theorem_3_1
-- name    : TemporalVoter.theorem_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:14:33.450137+00:00
-- url     : https://prove2.me/theorems/80e033c8-de6d-476a-b524-af1e896d8bce
-- title:
--   Theorem 3.1 — two-opinion consensus within $\Delta_0+\dots+\Delta_J$ with probability at least $1/2$
-- statement:
--   There is a constant $b>0$ such that the following holds. Consider the standard two-opinion voter model on a temporal graph $\mathcal G$ with fixed vertex degrees and minimum degree $d_{\min}$, with arbitrary initial minority set $s_0$. Let $\Delta_0,\Delta_1,\ldots\ge1$ be integers and $\phi_0,\phi_1,\ldots\in[0,1]$ reals, let $I^-_j=\Delta_0+\dots+\Delta_{j-1}$, $I^+_j=I^-_j+\Delta_j-1$, $I_j=[I^-_j,I^+_j]$, and suppose $\phi^{I_j}(\mathcal G)\ge\phi_j$ for all $j\ge0$. Let
--   $$J=\min\Bigl\{j:\ \sum_{\ell=0}^{j}\phi_\ell\ge b\Bigl(\frac{\mathrm{Vol}(s_0)}{d_{\min}}+\log\bigl(1+\mathrm{Vol}(s_0)\bigr)\Bigr)\Bigr\},$$
--   where we require $J<\infty$. Then with probability at least $1/2$ the consensus time is at most $\Delta_0+\dots+\Delta_J$.
--
--   The constant $b$ is absolute: it is chosen before the graph, the initial state and the sequences $\Delta,\phi$. This is the heart of the upper bound; the multi-opinion Theorem 1.3 is reduced to it.
--
--   Differences from the source:
--   - encoding: the voter process (ξ_t : t ≥ 0) of Definition 1.2 on some probability space → the path measure voterLaw on ℕ → (V → Fin k), built by Ionescu-Tulcea (Kernel.traj) from the synchronous lazy step kernels of Definition 1.2, started at σ₀; reason: the process is constructed from its definition (paper.md R4); every event and expectation of the paper is one of this law
--   - encoding: J = min{j : …} where we require J < ∞ → a hypothesis hJ : ∃ j, threshold ≤ ∑_{ℓ ≤ j} φ_ℓ, and J := Nat.find hJ; reason: paper.md R6; the same J
--   - encoding: the consensus time is at most x → the event ∃ t ≤ x with ξ_t constant; reason: the consensus time is the first t with ξ_t constant (Definition 1.2), so this is the same event (paper.md R2)
--   - encoding: arbitrary initial minority set s_0 → arbitrary initial state σ₀ : V → Fin 2, with s_0 its minority set; reason: every set of volume at most half the total is the minority set of the state that gives it opinion 0
--   - encoding: a sequence of undirected graphs on a common vertex set V(G) with common degree d(v) → T : TemporalGraph V: a Fintype V, G t : SimpleGraph V, and the degree data d with degree_eq and one_le_d; reason: the paper's graphs are plain finite graphs (n vertices, m = ½ ∑ d(v) edges, e_t counts edges); no loop or parallel edge occurs in them, the self-loop of Figure 1 only pictures laziness
-- source:
--   Rocha Avila, Dell, Lapinskas, Temporal Conductance and Bounds on the Voter Model for Dynamic Networks, arXiv:2606.13374 (2 Nov 2026), Theorem 3.1, p.15 (restated p.22)

import Mathlib
import Definitions.Def_TemporalVoter_TwoOpinionBound

namespace TemporalVoter

/-- **Theorem 3.1** (arXiv:2606.13374, version of 2 Nov 2026, p.15, restated p.22): there is a
constant `b > 0` such that, for the standard two-opinion voter model on any temporal graph with
fixed degrees and minimum degree `d_min`, with arbitrary initial minority set `s₀`, all integers
`Δ_0, Δ_1, … ≥ 1` and reals `φ_0, φ_1, … ∈ [0, 1]` with `φ^{I_j}(G) ≥ φ_j` for all `j`, if
`J = min{j : ∑_{ℓ=0}^{j} φ_ℓ ≥ b(Vol(s₀)/d_min + log(1 + Vol(s₀)))} < ∞`, then with probability at
least `1/2` the consensus time is at most `Δ_0 + ⋯ + Δ_J` (`TwoOpinionBound b`). The constant `b`
is chosen before the graph. -/
theorem theorem_3_1 : ∃ b : ℝ, 0 < b ∧ TwoOpinionBound b := by sorry

end TemporalVoter
