-- Prove2me | Theorems.Thm_PaceSSSP517_Certified_sampling
-- name    : PaceSSSP517.Certified.sampling
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:03:53.867077+00:00
-- url     : https://prove2.me/theorems/6a9dfec4-01e9-4c5d-9d1d-85a33fe90c46
-- title:
--   Lemma 3.4 — Conditional sampling bound
-- statement:
--   Fix any reachable history immediately before Pass A. Its weights $q_e^{(r)}$, total weight $Q^{(r)}$ and rate $s_r$ are fixed; its fresh sample still consists of independent Bernoulli choices with the prescribed probabilities. With $\theta=\varepsilon/(10kn^{1/k})$, the computed profile satisfies
--
--   $$\Pr_{F_r}\!\left[W_r\le2\theta Q^{(r)}\;\text{and}\;\rho_r\le2\theta\right]\ge1-n^{-n}.$$
--
--   Here $W_r$ is the total current weight of all edges failing the resulting local shortest-path profile, and $\rho_r=W_r/Q^{(r)}$. The two inequalities are equivalent because $Q^{(r)}>0$. The claim is conditional on every legal prehistory, including histories with earlier large violating fractions; it does not assume the desired estimate in the run definition.
--
--   Differences from the source:
--   - encoding: finite undirected positive-real weighted graphs and one-based rounds → Fin n vertices, each edge stored once with its smaller endpoint first, and list position j-1 for round j; source vertex s₀ and real sample budget s; reason: these are bijective naming and indexing conventions; no parallel edges or weight restriction is added
--   - encoding: compute exact source distances and a shortest-path tree of the observed subgraph → n-1 synchronous local Bellman–Ford relaxations and the least numbered tight predecessor at each non-source vertex; reason: this fixes a permitted deterministic tie rule using only the observed subgraph; its exactness and finite path realization are proof obligations, not run assumptions
--   - encoding: real lower bound on success probability → normalized finite-support PMF probability in ENNReal, lower bounded by ENNReal.ofReal of the stated real expression; reason: when the displayed real lower bound is negative both assertions are automatic; otherwise ofReal preserves the inequality exactly
-- source:
--   Sarwan Ali, STOC 2027 submission #517 (October 2026), p. 7, Lemma 3.4; p. 17, Appendix A.3

import Definitions.Def_PaceSSSP517_Certified_Law

set_option autoImplicit false
open scoped ENNReal NNReal

namespace PaceSSSP517.Certified

/-- Lemma 3.4, p.7; proof A.3 p.17. Every reachable pre-Pass-A history,
with its exact conditional independent sampling kernel. -/
theorem sampling
    (n k : ℕ) (ε : ℝ) (G : WeightedGraph n) (H : Finset (Edge n))
    (s₀ : Fin n)
    (hparams : Parameters n k ε) (hG : Connected G.edges)
    (hH : IsSpanner G H (2 * (k : ℝ) - 1 + ε))
    (a : State n) (ha : PreHistory G H s₀ k ε a) :
    ENNReal.ofReal (1 - ((n : ℝ)^n)⁻¹) ≤
      probability (sampleLaw G a) {F |
        violatingWeight G a (freshProfile G H s₀ a F) ≤ 2 * theta n k ε * a.Q ∧
        fraction G a (freshProfile G H s₀ a F) ≤ 2 * theta n k ε} := by sorry

end PaceSSSP517.Certified
