-- Prove2me | Theorems.Thm_SplitPMSGame_pmsGame_totallyBalanced
-- name    : SplitPMSGame.pmsGame_totallyBalanced
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:13:18.202295+00:00
-- url     : https://prove2.me/theorems/776ca63a-3a3b-48ed-915a-da650012dc43
-- title:
--   Theorem 4 — the PMS game under job splitting is totally balanced
-- statement:
--   Let $N$ be a finite set of players, player $i$ owning machines of total speed $v(\{i\})\in\mathbb Q_{>0}$, and let finitely many jobs with requirements $p_j\ge0$ be given, each job owned by a player and each player owning a job. Let
--   $$
--   P(S)=\frac1{v(S)}\sum_{k=1}^{\psi(S)}(\psi(S)-k+1)\,p^S_k
--   $$
--   be the PMS game of equation (1). Then $(N,P)$ is **totally balanced**: for every coalition $S\subseteq N$ there is a cost allocation $x$ with
--   $$
--   \sum_{i\in S}x_i=P(S)\qquad\text{and}\qquad \sum_{i\in T}x_i\le P(T)\ \text{ for every }T\subseteq S.
--   $$
--
--   The game is neither monotone nor concave and its nonnegative core can be empty (Example 4), so no standard sufficient condition for total balancedness applies.
--
--   Differences from the source:
--   - generalization: N = {1, …, n} with n ≥ 2 → any finite type N; reason: the case n ≥ 2 is a special case; the statement does not use n ≥ 2
--   - generalization: jobs indexed 1, …, ψ(N) in nondecreasing order of requirement → any indexing p : Fin ψ → ℝ (no Monotone hypothesis); reason: (1) is evaluated on the sorted requirements, so P is invariant under relabelling the jobs; the paper's indexed instances are a special case
--   - generalization: a player with no jobs has one empty job (requirement 0); a player with jobs owns none of requirement 0 → f surjective onto N and p ≥ 0; a player may own zero-requirement jobs alongside positive ones; reason: every instance of the paper is allowed; a job of requirement 0 adds 0 to (1) and leaves the weights of the other jobs unchanged
--   - encoding: P defined by equation (1) → pmsCost p f v, equation (1) with sorted requirements; reason: the paper takes (1) as the characteristic function (p.2239)
--   - encoding: each player i owns a nonempty set M({i}) of machines of positive rational speeds → v : N → ℚ, the total speed v({i}), cast to ℝ; reason: the paper notes that the number of machines in M({i}) is immaterial (p.2238); only v(S) enters (1)
--   - encoding: core allocation of the subgame (S, P) in ℝ^S → x : N → ℝ, only the coordinates in S constrained; reason: Lean convention; same allocations
-- source:
--   Alon, Anily, The Basic Core of a Parallel Machines Scheduling Game, MSOM 25(6) (2023), doi:10.1287/msom.2021.0337, Theorem 4, p.2244 (PDF p.13); model §4, pp.2237–2239 (PDF pp.6–8)

import Mathlib
import Definitions.Def_SplitPMSGame_IsCoreAlloc
import Definitions.Def_SplitPMSGame_pmsCost

namespace SplitPMSGame

/-- **Theorem 4** (Alon, Anily, *The Basic Core of a Parallel Machines Scheduling Game*, MSOM
25(6) (2023), p.2244): "The PMS game (N, P) is totally balanced." For every finite set of
players with positive rational machine speeds and every finite set of jobs with nonnegative
processing requirements, each job owned by a player and each player owning a job, the cost game
`P(S) = (1/v(S)) ∑_{k=1}^{ψ(S)} (ψ(S) − k + 1) p^S_k` of equation (1) has, for every coalition
`S`, a cost allocation `x` with `∑_{i∈S} xᵢ = P(S)` and `∑_{i∈T} xᵢ ≤ P(T)` for every `T ⊆ S`.

**Formalization Note** Players `N` (any finite type, `n ≥ 2` not needed); jobs `Fin ψ` with
requirements `p` and father map `f` (surjective: every player has at least one job, possibly of
requirement `0`); per-player total speeds `v : N → ℚ`, positive. The jobs need not be indexed in
nondecreasing order of requirement, since equation (1) is evaluated on the sorted requirements;
a player may own zero-requirement jobs alongside positive ones. -/
theorem pmsGame_totallyBalanced {N : Type*} [Fintype N] [DecidableEq N] {ψ : ℕ}
    (p : Fin ψ → ℝ) (f : Fin ψ → N) (v : N → ℚ) (hv : ∀ i, 0 < v i) (hp : ∀ j, 0 ≤ p j)
    (hf : Function.Surjective f) :
    TotallyBalanced (pmsCost p f v) := by sorry

end SplitPMSGame
