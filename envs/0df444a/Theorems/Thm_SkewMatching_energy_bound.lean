-- Prove2me | Theorems.Thm_SkewMatching_energy_bound
-- name    : SkewMatching.energy_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:13:12.920906+00:00
-- url     : https://prove2.me/theorems/689ecea4-826d-403e-a021-5d492cfc7e9d
-- title:
--   §3.4, p.8 — the total number of barrier toggle operations is O(n² log(2U))
-- statement:
--   There is an absolute constant $c>0$ such that for every simple skew-symmetric graph $G$ on $n\ge 1$ vertices, every source $s$, every $K\ge 1$, every $U\ge 1$, and every reachability policy, every state reachable with positive probability from the start of the algorithm of §3.3 has made at most
--
--   $$
--   c\,n^2\log(2U)
--   $$
--
--   barrier toggle operations.
--
--   The bound holds on all runs, not merely with high probability. It accounts for the number of operations, each of which the sampling data structure then carries out in $n^{o(1)}$ time.
--
--   Differences from the source:
--   - generalization: the regular reachability algorithm of [GK96] → every ReachPolicy, a deterministic map obeying Lemma 23; reason: the paper's search is one policy, and the energy argument uses only (Pause) and (Progress)
--   - reading: simple: no parallel edges between any two vertices → Simple: (tail, head) is injective, so antiparallel pairs and loops are allowed; reason: the wording of p.1 read per ordered pair; §2.3 says the algorithm also handles a constant number of parallel edges, and loops carry only cycle flow
--   - encoding: O(n² log(2U)) for polynomially bounded U → c n² log(2U) with an absolute c, for every U ≥ 1 and n ≥ 1; reason: the printed O(·), with a constant before the graph; U ≥ 1 is what x_e ∈ [1, U] needs
--   - encoding: the number of operations on the run → the toggle counter of every state in the support of the law after t steps, for every t; reason: every run prefix of positive probability ends in such a state
--   - encoding: a parameter K → K a natural number with K ≥ 1; reason: K is a positive parameter throughout the paper ("2n/K", "K/2"); at K = 0 Lemma 15 fails and the process need not ever find a negative edge
-- source:
--   Li, Li, Zhang, Maximum Cardinality Matching in n^{2+o(1)} Time, STOC 2027 submission (manuscript sha256 3fc151f5…), §3.4, p.8

import Mathlib
import Definitions.Def_SkewMatching_ProcState

namespace SkewMatching

/-- **Energy bound**, §3.4, p.8. "Therefore, the total number of barrier toggle operations that sample a positively charged edge is at most O(n² log(2U)). Combined with the O(n²) operations that sample a negatively charged edge, the total number of barrier toggle operations is at most O(n² log(2U))."

Li, Li, Zhang, *Maximum Cardinality Matching in n^{2+o(1)} Time*, STOC 2027 submission (manuscript sha256 3fc151f5…), §3.4, p.8.

**Formalization Note.** Deterministic, on all runs: every state of positive probability after any number of steps has made at most `c n² log(2U)` toggles. The constant is absolute and comes before the graph. The process is the algorithm of §3.3 run from its start, for every
reachability policy obeying Lemma 23 (the paper's search is one). `Simple` is the standing assumption of §2.3; `U ≥ 1` makes `x_e ∈ [1, U]` possible. -/
theorem energy_bound :
    ∃ c : ℝ, 0 < c ∧ ∀ (n : ℕ), 1 ≤ n → ∀ {E : Type} [Fintype E] (G : SkewGraph (Fin n) E),
      G.Simple → ∀ (s : Fin n) (K : ℕ), 1 ≤ K → ∀ (U : ℝ), 1 ≤ U → ∀ (π : ReachPolicy G s) (t : ℕ),
        ∀ σ ∈ (ProcState.law G s K U π t).support,
          (σ.toggles : ℝ) ≤ c * (n : ℝ) ^ 2 * Real.log (2 * U) := by sorry

end SkewMatching
