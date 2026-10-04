-- Prove2me | Theorems.Thm_PolylogKServer_Main_polylog_competitive
-- name    : PolylogKServer.Main.polylog_competitive
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T05:28:59.312225+00:00
-- url     : https://prove2.me/theorems/b5077a04-24fd-4ae4-9b63-c566c21712d7
-- title:
--   Theorem 1 — randomized k-server is O(log² k log³ n log log n)-competitive on every n-point metric
-- statement:
--   There is a universal constant $C>0$ such that for every $k\ge2$, every finite metric space $M$ with $n\ge3$ points and every initial configuration $C_0$ of the $k$ servers, there is a randomized online k-server algorithm starting at $C_0$ that is
--   $$
--   C\,\log^2 k\,\log^3 n\,\log\log n\text{-competitive}
--   $$
--   against an oblivious adversary: its expected cost on every request sequence $\rho$ is at most $C\log^2k\log^3n\log\log n\cdot\mathrm{OPT}(C_0,\rho)+a$, where $\mathrm{OPT}(C_0,\rho)$ is the optimal offline cost of serving $\rho$ from $C_0$ and $a$ is a constant independent of $\rho$.
--
--   This is the first polylogarithmic competitive ratio for randomized k-server on general finite metrics; before it, nothing better than the deterministic $2k-1$ was known.
--
--   **Formalization Note** The randomized algorithm and competitiveness are the published `KServer.RandomizedAlgorithm` and `IsCompetitiveFrom` (definitions `KServer_model`, `KServer_randomized`). The $O(\cdot)$ is a universal constant quantified before $k$, $M$ and $C_0$. Logarithms are natural. The guards $k\ge2$ and $n\ge3$ make $\log^2k>0$ and $\log\log n>0$. The case $k\ge n$ is included.
-- source:
--   Bansal, Buchbinder, Mądry, Naor, A Polylogarithmic-Competitive Algorithm for the k-Server Problem, arXiv:1110.1580v1, p. 2, Theorem 1 (proof p. 9)

import Mathlib
import Definitions.Def_KServer_model
import Definitions.Def_KServer_randomized

namespace PolylogKServer.Main

/-- **Theorem 1** (Bansal–Buchbinder–Mądry–Naor, arXiv:1110.1580v1, p. 2). There is a universal
constant `C > 0` such that for every `k ≥ 2`, every finite metric space `M` with `n ≥ 3` points
and every initial configuration `C₀` of the `k` servers, some randomized online k-server
algorithm starting at `C₀` is `C · log² k · log³ n · log log n`-competitive against an
oblivious adversary. -/
theorem polylog_competitive :
    ∃ C : ℝ, 0 < C ∧ ∀ (k : ℕ) (M : Type) [MetricSpace M] [Fintype M]
      (C₀ : KServer.Config k M), 2 ≤ k → 3 ≤ Fintype.card M →
      ∃ A : KServer.RandomizedAlgorithm k M,
        A.IsCompetitiveFrom C₀
          (C * Real.log k ^ 2 * Real.log (Fintype.card M) ^ 3 *
            Real.log (Real.log (Fintype.card M))) := by sorry

end PolylogKServer.Main
