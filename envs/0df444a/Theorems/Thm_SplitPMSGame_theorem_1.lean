-- Prove2me | Theorems.Thm_SplitPMSGame_theorem_1
-- name    : SplitPMSGame.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:14:06.075635+00:00
-- url     : https://prove2.me/theorems/565f29e7-9a5b-452b-a403-18cf562b926e
-- title:
--   Theorem 1 — the PMS game is $\sum_j\Delta_jF^{(j)}$
-- statement:
--   Under the assumptions of Lemma 1, the constrained PMS game satisfies, for every coalition $S\subseteq N$,
--   $$
--   F(J(S))=\sum_{j=1}^{\psi(N)}\Delta_j\,F^{(j)}(J(S)),
--   $$
--   where $F^{(j)}$ is the $j$-th constrained basic PMS game: the same players, jobs and speeds, with the $0$–$1$ requirement vector whose first $j-1$ entries are $0$.
--
--   Together with the additivity and scaling properties of the core, it reduces total balancedness of the PMS game to that of the CB games.
--
--   Differences from the source:
--   - encoding: jobs indexed 1, …, ψ(N) in nondecreasing order of requirement, p₀ = 0 → jobs Fin ψ with Monotone p; the paper's job j is the index j − 1; reason: Lean convention; same instances
--   - encoding: F^(j)(J(S)), the CB game with job-player speeds v({f(k)})/ψ({f(k)}) → pmsCost (basicReq j) f v S; reason: the job-player speeds of J(S) sum to v(S), so the CB cost is (1) for the 0–1 vector with the coalition speed v(S)
--   - encoding: P(S) = F(J(S)), the characteristic function of the constrained PMS game on feasible coalitions J(S) → pmsCost p f v S for every S ⊆ N, defined by equation (1); reason: the paper takes (1) as the characteristic function and states F(J(S)) = P(S) (p.2239)
--   - encoding: each player i owns a nonempty set M({i}) of machines of positive rational speeds → v : N → ℚ, the total speed v({i}), cast to ℝ; reason: the paper notes that the number of machines in M({i}) is immaterial (p.2238); only v(S) enters (1)
--   - generalization: N = {1, …, n} with n ≥ 2 → any finite type N; reason: the case n ≥ 2 is a special case; the statement does not use n ≥ 2
--   - generalization: a player with no jobs has one empty job (requirement 0); a player with jobs owns none of requirement 0 → f surjective onto N and p ≥ 0; a player may own zero-requirement jobs alongside positive ones; reason: every instance of the paper is allowed; a job of requirement 0 adds 0 to (1) and leaves the weights of the other jobs unchanged
-- source:
--   Alon, Anily, The Basic Core of a Parallel Machines Scheduling Game, MSOM 25(6) (2023), doi:10.1287/msom.2021.0337, Theorem 1, eq. (7), p.2242 (PDF p.11)

import Mathlib
import Definitions.Def_SplitPMSGame_pmsCost
import Definitions.Def_SplitPMSGame_marginalInc

namespace SplitPMSGame

/-- **Theorem 1** (Alon, Anily, *The Basic Core of a Parallel Machines Scheduling Game*, MSOM
25(6) (2023), p.2242): the constrained PMS game `(J(N), 𝒞, F)` satisfies
`F(J(S)) = ∑_{j=1}^{ψ(N)} Δⱼ F^(j)(J(S))` for every coalition `S`, where `F^(j)` is the `j`-th
constrained basic (CB) PMS game: the same players, speeds and feasible coalitions, with the
`0`–`1` requirement vector whose first `j − 1` entries are `0`.

**Formalization Note** `F(J(S)) = P(S) = pmsCost p f v S` (p.2239), and
`F^(j)(J(S)) = pmsCost (basicReq j) f v S` is the PMS cost of the `j`-th CB requirement vector,
not its closed form (6). Lean index `j` is the paper's `j + 1`. -/
theorem theorem_1 {N : Type*} [Fintype N] [DecidableEq N] {ψ : ℕ} (p : Fin ψ → ℝ)
    (f : Fin ψ → N) (v : N → ℚ) (hv : ∀ i, 0 < v i) (hp : ∀ j, 0 ≤ p j) (hmono : Monotone p)
    (hf : Function.Surjective f) (S : Finset N) :
    pmsCost p f v S = ∑ j : Fin ψ, marginalInc p j * pmsCost (basicReq j) f v S := by sorry

end SplitPMSGame
