-- Prove2me | Theorems.Thm_SplitPMSGame_theorem_3
-- name    : SplitPMSGame.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:13:36.749721+00:00
-- url     : https://prove2.me/theorems/b6636d74-8bf2-40bc-b45a-450f04ebefaf
-- title:
--   Theorem 3 — $(N,P)$ is totally balanced iff all UCB PMS games are
-- statement:
--   Assume that the jobs are indexed in nondecreasing order of their requirements $p_j\ge0$, the speeds are positive rationals, every player owns a job, and (Assumption 1) every player's speed is $v(\{i\})=\psi(\{i\})\,m(i)$ for a natural number $m(i)$. Then the PMS game $(N,P)$ is totally balanced if and only if, for every $j=1,\dots,\psi(N)$, the UCB PMS game $(J^U(N),\mathcal C^U,F^{(j)}_U)$ is totally balanced as a constrained game whose feasible coalitions are the sets $J^U(S)$, $S\subseteq N$.
--
--   This is the reduction that, with Observation 1 and Theorem 2, proves Theorem 4.
--
--   Differences from the source:
--   - encoding: jobs indexed 1, …, ψ(N) in nondecreasing order of requirement, p₀ = 0 → jobs Fin ψ with Monotone p; the paper's job j is the index j − 1; reason: Lean convention; same instances
--   - encoding: Assumption 1: v({i})/ψ({i}) is a natural number → m : N → ℕ with v i = ψ({i}) · m i; reason: same assumption; m(i) is the speed of player i's job players
--   - encoding: UCB game: each job player ℓ split into v′({ℓ}) unit-speed players, one with ℓ's requirement in the j-th CB game, the others 0 → UnitPlayer f m = Σ ℓ, Fin (m (f ℓ)); ucbReq gives 1 to (ℓ, 0) iff ℓ ≥ j; ucbCost is (1) with unit speeds; Lean j is the paper's j + 1; reason: same game
--   - reading: a constrained game (Ñ, 𝒞, G̃) is totally balanced (term used, not defined) → ConstrainedTotallyBalanced: for every S ⊆ N some y : Ñ → ℝ has Σ_{Π(S)} y = G̃(Π(S)) and Σ_{Π(T)} y ≤ G̃(Π(T)) for all T ⊆ S; reason: Definition 3 applied to every constrained subgame on a feasible coalition Π(S), whose feasible subcoalitions are the Π(T), T ⊆ S
--   - encoding: each player i owns a nonempty set M({i}) of machines of positive rational speeds → v : N → ℚ, the total speed v({i}), cast to ℝ; reason: the paper notes that the number of machines in M({i}) is immaterial (p.2238); only v(S) enters (1)
--   - generalization: N = {1, …, n} with n ≥ 2 → any finite type N; reason: the case n ≥ 2 is a special case; the statement does not use n ≥ 2
--   - generalization: a player with no jobs has one empty job (requirement 0); a player with jobs owns none of requirement 0 → f surjective onto N and p ≥ 0; a player may own zero-requirement jobs alongside positive ones; reason: every instance of the paper is allowed; a job of requirement 0 adds 0 to (1) and leaves the weights of the other jobs unchanged
-- source:
--   Alon, Anily, The Basic Core of a Parallel Machines Scheduling Game, MSOM 25(6) (2023), doi:10.1287/msom.2021.0337, Theorem 3, p.2244 (PDF p.13); Assumption 1, p.2240 (PDF p.9); §5.1.2, p.2242 (PDF p.11)

import Mathlib
import Definitions.Def_SplitPMSGame_IsCoreAlloc
import Definitions.Def_SplitPMSGame_ConstrainedTotallyBalanced
import Definitions.Def_SplitPMSGame_pmsCost
import Definitions.Def_SplitPMSGame_ucbGame

namespace SplitPMSGame

/-- **Theorem 3** (Alon, Anily, *The Basic Core of a Parallel Machines Scheduling Game*, MSOM
25(6) (2023), p.2244): the PMS game `(N, P)` is totally balanced if and only if the UCB PMS
games `(J^U(N), 𝒞^U, F^(j)_U)`, `j = 1, …, ψ(N)`, are totally balanced.

**Formalization Note** Assumption 1 (p.2240) is in force from §5 on: the job players of each
player `i` have the natural speed `m(i) = v({i})/ψ({i})`, i.e. `v({i}) = ψ({i}) · m(i)`. Jobs
are indexed `Fin ψ` in nondecreasing order of requirement (`Monotone p`), `p ≥ 0`, speeds are
positive rationals and every player owns a job (`f` surjective). The UCB games are constrained
games whose feasible coalitions are the sets `J^U(S)` of unit-speed descendants of the
coalitions `S ⊆ N` (`ucbFather` is the splitting scheme); Lean index `j` is the paper's
`j + 1`. -/
theorem theorem_3 {N : Type*} [Fintype N] [DecidableEq N] {ψ : ℕ} (p : Fin ψ → ℝ)
    (f : Fin ψ → N) (v : N → ℚ) (m : N → ℕ) (hv : ∀ i, 0 < v i) (hp : ∀ j, 0 ≤ p j)
    (hmono : Monotone p) (hf : Function.Surjective f)
    (hvm : ∀ i, v i = (jobCount f i : ℚ) * (m i : ℚ)) :
    TotallyBalanced (pmsCost p f v) ↔
      ∀ j : Fin ψ, ConstrainedTotallyBalanced (ucbFather f m) (ucbCost f m j) := by sorry

end SplitPMSGame
