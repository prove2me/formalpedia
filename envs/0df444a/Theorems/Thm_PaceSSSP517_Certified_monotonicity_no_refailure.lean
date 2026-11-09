-- Prove2me | Theorems.Thm_PaceSSSP517_Certified_monotonicity_no_refailure
-- name    : PaceSSSP517.Certified.monotonicity_no_refailure
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:02:48.285216+00:00
-- url     : https://prove2.me/theorems/a30c6d5b-1d2e-4b3d-92a6-cfd0d670b856
-- title:
--   Lemma 3.1 — Monotonicity and no re-failure
-- statement:
--   Consider any finite executed prefix of Algorithm 1 on a connected graph with the standing parameters and its initial spanner. Every round tree realizes its local source-distance profile. For every pair of consecutive executed rounds,
--
--   $$T_r\subseteq G_{r+1},\qquad \operatorname{dist}_G\le d_{r+1}\le d_r.$$
--
--   Every edge in $G_r$ satisfies the triangle inequality for $d_r$. Every edge retained in $P_r$ fails in no later executed round. In particular, a violator stored in a bulk round never fails again. These conclusions are deterministic, without any restriction on the sampling outcome.
--
--   The statement also makes explicit that local distances are finite and realized by weighted walks. This is the operational meaning of Algorithm 1's exact shortest-path calculation. The result supplies the monotonicity and persistence needed by the sampling and certificate statements.
--
--   Differences from the source:
--   - encoding: finite undirected positive-real weighted graphs and one-based rounds → Fin n vertices, each edge stored once with its smaller endpoint first, and list position j-1 for round j; source vertex s₀ and real sample budget s; reason: these are bijective naming and indexing conventions; no parallel edges or weight restriction is added
--   - encoding: compute exact source distances and a shortest-path tree of the observed subgraph → n-1 synchronous local Bellman–Ford relaxations and the least numbered tight predecessor at each non-source vertex; reason: this fixes a permitted deterministic tie rule using only the observed subgraph; its exactness and finite path realization are proof obligations, not run assumptions
--   - encoding: connected graphs and finite computed shortest-path distances → ENNReal path infima with real profiles and explicit finiteness and attained-path conclusions; reason: empty path families have genuine infinite distance; the connected positive-weight source instances have attained finite minima, so no default toReal value can satisfy the goal
--   - encoding: the loop stops before line 6 and Appendix A.5 uses weights through the round cap → a virtual update recursion followed by its prefix through the first stop; later virtual rounds and the terminal virtual update are not executed or charged; reason: the projected law has exactly the original conditional kernels before stopping and absorbing output thereafter; only its executed prefix enters the goal
-- source:
--   Sarwan Ali, STOC 2027 submission #517 (October 2026), p. 6, Lemma 3.1; p. 17, Appendix A.1

import Definitions.Def_PaceSSSP517_Certified_Algorithm

set_option autoImplicit false
open scoped ENNReal NNReal

namespace PaceSSSP517.Certified

/-- Lemma 3.1, p.6; proof A.1 p.17. Only executed rounds are asserted.
Finiteness and path attainment make every use of real distances meaningful. -/
theorem monotonicity_no_refailure
    (n k : ℕ) (ε : ℝ) (G : WeightedGraph n) (H : Finset (Edge n))
    (s₀ : Fin n)
    (hparams : Parameters n k ε) (hG : Connected G.edges)
    (hH : IsSpanner G H (2 * (k : ℝ) - 1 + ε))
    (Fs : List (Finset (Edge n))) (hFs : SampleTrace G H s₀ k ε Fs)
    (hexecuted : execution (trajectory G H s₀ k ε Fs).rounds =
      (trajectory G H s₀ k ε Fs).rounds) :
    let ts := (trajectory G H s₀ k ε Fs).rounds
    ∀ r ∈ past Fs.length,
      let a := trajectory G H s₀ k ε (Fs.take (r - 1))
      let t := roundAt ts r
      let K := roundGraph G H a (Fs.getD (r - 1) ∅)
      IsShortestTree G K s₀ t.tree ∧
      (∀ x, t.d x = distance G K s₀ x) ∧
      (∀ x, edistance G K s₀ x ≠ ⊤ ∧
        ∃ p, IsWalk K s₀ x p ∧ pathCost G p = t.d x) ∧
      (∀ e ∈ K, ¬ fails G t.d e) ∧
      (r + 1 ≤ Fs.length →
        t.tree ⊆ roundGraph G H (trajectory G H s₀ k ε (Fs.take r)) (Fs.getD r ∅) ∧
        ∀ x, distance G G.edges s₀ x ≤ profile ts (r + 1) x ∧
          profile ts (r + 1) x ≤ t.d x) ∧
      (∀ e ∈ pinned G (trajectory G H s₀ k ε (Fs.take r)),
        ∀ r' ∈ past Fs.length, r < r' → ¬ fails G (profile ts r') e) ∧
      (t.bulk = true → t.stopping = false → ∀ e ∈ violators G t.d,
        ∀ r' ∈ past Fs.length, r < r' → ¬ fails G (profile ts r') e) := by sorry

end PaceSSSP517.Certified
