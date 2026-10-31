-- Prove2me | Theorems.Thm_SplitPMSGame_lemma_1
-- name    : SplitPMSGame.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:13:53.124229+00:00
-- url     : https://prove2.me/theorems/1a3f783a-fcc5-4263-838f-77971cd73f5e
-- title:
--   Lemma 1 — $P(S)$ as a nonnegative combination of the marginal increments
-- statement:
--   Let the jobs be indexed $1,\dots,\psi(N)$ in nondecreasing order of their requirements $p_j\ge0$, with $p_0=0$, the speeds be positive rationals and every player own a job. Then every marginal increment $\Delta_j=p_j-p_{j-1}$ is nonnegative, and for every coalition $S\subseteq N$
--   $$
--   P(S)=F(J(S))=\sum_{j=1}^{\psi(N)}\Delta_j\,\frac{K_{J(S)}(j)\,\big(K_{J(S)}(j)+1\big)}{2v(S)},
--   $$
--   where $K_{J(S)}(j)$ is the number of jobs of $S$ whose index is at least $j$.
--
--   This presentation of the characteristic function as a nonnegative linear combination is the starting point of the decomposition into CB games.
--
--   Differences from the source:
--   - encoding: jobs indexed 1, …, ψ(N) in nondecreasing order of requirement, p₀ = 0 → jobs Fin ψ with Monotone p; the paper's job j is the index j − 1; reason: Lean convention; same instances
--   - reading: K_{J(S)}(j) = ψ(S) + 1 − ℓ^S(j) with the printed ℓ^S(j) = {ℓ : j^S_{ℓ−1} ≤ j < j^S_ℓ} → countFrom f S j = #{k ∈ J(S) : k ≥ j}; reason: the sentence after (4) and the proof say 'at least as large as j'; the printed set counts indices > j and makes Lemma 1 false (one player, one job p = 1, v = 1: P = 1, the sum is 0)
--   - encoding: the middle term Σ_ℓ C_{j^S_ℓ} of (5) → omitted; reason: it is the total completion time, i.e. equation (1) itself
--   - encoding: a nonnegative linear combination → the conjunct ∀ j, 0 ≤ Δ j; reason: the coefficients K(K+1)/(2v(S)) are nonnegative by construction; the content of 'nonnegative' is Δⱼ ≥ 0
--   - encoding: P(S) = F(J(S)), the characteristic function of the constrained PMS game on feasible coalitions J(S) → pmsCost p f v S for every S ⊆ N, defined by equation (1); reason: the paper takes (1) as the characteristic function and states F(J(S)) = P(S) (p.2239)
--   - encoding: each player i owns a nonempty set M({i}) of machines of positive rational speeds → v : N → ℚ, the total speed v({i}), cast to ℝ; reason: the paper notes that the number of machines in M({i}) is immaterial (p.2238); only v(S) enters (1)
--   - generalization: N = {1, …, n} with n ≥ 2 → any finite type N; reason: the case n ≥ 2 is a special case; the statement does not use n ≥ 2
--   - generalization: a player with no jobs has one empty job (requirement 0); a player with jobs owns none of requirement 0 → f surjective onto N and p ≥ 0; a player may own zero-requirement jobs alongside positive ones; reason: every instance of the paper is allowed; a job of requirement 0 adds 0 to (1) and leaves the weights of the other jobs unchanged
-- source:
--   Alon, Anily, The Basic Core of a Parallel Machines Scheduling Game, MSOM 25(6) (2023), doi:10.1287/msom.2021.0337, Lemma 1, eq. (5), p.2240 (PDF p.9)

import Mathlib
import Definitions.Def_SplitPMSGame_pmsCost
import Definitions.Def_SplitPMSGame_marginalInc

namespace SplitPMSGame

/-- **Lemma 1** (Alon, Anily, *The Basic Core of a Parallel Machines Scheduling Game*, MSOM 25(6)
(2023), p.2240): the characteristic function value of every feasible coalition `J(S)` of the
constrained PMS game is the nonnegative linear combination of the marginal increments
`Δⱼ = pⱼ − pⱼ₋₁ ≥ 0` (`p₀ = 0`)
`P(S) = F(J(S)) = ∑_{j=1}^{ψ(N)} Δⱼ K_{J(S)}(j)(K_{J(S)}(j)+1) / (2v(S))`, where `K_{J(S)}(j)` is
the number of jobs of `J(S)` whose index is at least `j`.

**Formalization Note** Jobs are indexed `Fin ψ` in nondecreasing order of requirement
(`Monotone p`), with requirements `p ≥ 0`, positive rational speeds, and every player owning a
job (`f` surjective). The middle term `∑_ℓ C_{j^S_ℓ}` (the total completion time) is equation (1)
itself and is not restated. `F(J(S)) = P(S)` holds by definition (p.2239). -/
theorem lemma_1 {N : Type*} [Fintype N] [DecidableEq N] {ψ : ℕ} (p : Fin ψ → ℝ)
    (f : Fin ψ → N) (v : N → ℚ) (hv : ∀ i, 0 < v i) (hp : ∀ j, 0 ≤ p j) (hmono : Monotone p)
    (hf : Function.Surjective f) :
    (∀ j, 0 ≤ marginalInc p j) ∧
      ∀ S : Finset N, pmsCost p f v S =
        ∑ j : Fin ψ, marginalInc p j *
          (((countFrom f S j : ℝ) * ((countFrom f S j : ℝ) + 1)) / (2 * speed v S)) := by sorry

end SplitPMSGame
