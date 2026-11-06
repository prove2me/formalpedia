-- Prove2me | Theorems.Thm_TemporalVoter_theorem_1_3
-- name    : TemporalVoter.theorem_1_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:12:09.658385+00:00
-- url     : https://prove2.me/theorems/f02f291e-c162-4fb7-939c-dfd121d1661b
-- title:
--   Theorem 1.3 — consensus within $\Delta_0+\dots+\Delta_J$ for any interval partition, with probability at least $1/2$
-- statement:
--   There is a constant $b>0$ such that the following holds. Consider the standard voter model, with any number of opinions, on a temporal graph $\mathcal G$ with fixed vertex degrees, $m$ edges and minimum degree $d_{\min}$, with arbitrary initial state. Let $\Delta_0,\Delta_1,\ldots\ge1$ be integers and $\phi_0,\phi_1,\ldots\in[0,1]$ reals, let $I^-_j=\Delta_0+\dots+\Delta_{j-1}$, $I^+_j=I^-_j+\Delta_j-1$, $I_j=[I^-_j,I^+_j]$, and suppose $\phi^{I_j}(\mathcal G)\ge\phi_j$ for all $j\ge0$. Let
--   $$J=\min\Bigl\{j:\ \sum_{\ell=0}^{j}\phi_\ell\ge\frac{bm}{d_{\min}}\Bigr\},$$
--   where we require $J<\infty$. Then with probability at least $1/2$ the consensus time is at most $\Delta_0+\dots+\Delta_J$.
--
--   The constant $b$ is chosen before the graph, the number of opinions, the initial state and the sequences. Choosing all windows of the length that realises $\Phi(\mathcal G)$ gives Main Theorem 1.
--
--   Differences from the source:
--   - encoding: the voter process (ξ_t : t ≥ 0) of Definition 1.2 on some probability space → the path measure voterLaw on ℕ → (V → Fin k), built by Ionescu-Tulcea (Kernel.traj) from the synchronous lazy step kernels of Definition 1.2, started at σ₀; reason: the process is constructed from its definition (paper.md R4); every event and expectation of the paper is one of this law
--   - encoding: J = min{j : …} where we require J < ∞ → a hypothesis hJ : ∃ j, threshold ≤ ∑_{ℓ ≤ j} φ_ℓ, and J := Nat.find hJ; reason: paper.md R6; the same J
--   - encoding: the consensus time is at most x → the event ∃ t ≤ x with ξ_t constant; reason: the consensus time is the first t with ξ_t constant (Definition 1.2), so this is the same event (paper.md R2)
--   - encoding: κ a positive integer, σ₀ : V → {0, …, κ − 1} → k : ℕ and σ₀ : V → Fin k; reason: k = 0 admits a state only when V is empty, where consensus holds at time 0
--   - encoding: a sequence of undirected graphs on a common vertex set V(G) with common degree d(v) → T : TemporalGraph V: a Fintype V, G t : SimpleGraph V, and the degree data d with degree_eq and one_le_d; reason: the paper's graphs are plain finite graphs (n vertices, m = ½ ∑ d(v) edges, e_t counts edges); no loop or parallel edge occurs in them, the self-loop of Figure 1 only pictures laziness
-- source:
--   Rocha Avila, Dell, Lapinskas, Temporal Conductance and Bounds on the Voter Model for Dynamic Networks, arXiv:2606.13374 (2 Nov 2026), Theorem 1.3, p.7 (restated p.24)

import Mathlib
import Definitions.Def_TemporalVoter_voterLaw
import Definitions.Def_TemporalVoter_temporalConductance

open scoped Classical ENNReal

namespace TemporalVoter

/-- **Theorem 1.3 (Upper Bound)** (arXiv:2606.13374, version of 2 Nov 2026, p.7, restated p.24):
there is a constant `b > 0` such that, for the standard voter model on any temporal graph with fixed
degrees, `m` edges and minimum degree `d_min`, any number `k` of opinions and any initial state,
all integers `Δ_0, Δ_1, … ≥ 1` and reals `φ_0, φ_1, … ∈ [0, 1]` with `φ^{I_j}(G) ≥ φ_j` for all
`j`, if `J = min{j : ∑_{ℓ=0}^{j} φ_ℓ ≥ bm/d_min} < ∞`, then with probability at least `1/2` the
consensus time is at most `Δ_0 + ⋯ + Δ_J`.

**Formalization Note** `J` is `Nat.find` of the finiteness hypothesis `hJ`; "the consensus time is
at most `x`" is the event that some `t ≤ x` has all opinions equal. -/
theorem theorem_1_3 : ∃ b : ℝ, 0 < b ∧
    ∀ (V : Type) [Fintype V] (T : TemporalGraph V) (k : ℕ) (σ₀ : V → Fin k)
      (Δ : ℕ → ℕ) (φ : ℕ → ℝ), (∀ j, 1 ≤ Δ j) → (∀ j, 0 ≤ φ j ∧ φ j ≤ 1) →
      (∀ j, φ j ≤ intervalCond T (Iminus Δ j) (Iplus Δ j)) →
      ∀ hJ : ∃ j, b * T.m / T.dmin ≤ ∑ ℓ ∈ Finset.range (j + 1), φ ℓ,
      (1 / 2 : ℝ≥0∞) ≤ voterLaw T k σ₀
        {ω | ∃ t, t ≤ ∑ ℓ ∈ Finset.range (Nat.find hJ + 1), Δ ℓ ∧ IsConsensus (ω t)} := by sorry

end TemporalVoter
