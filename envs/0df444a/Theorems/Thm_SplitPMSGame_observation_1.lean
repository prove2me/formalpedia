-- Prove2me | Theorems.Thm_SplitPMSGame_observation_1
-- name    : SplitPMSGame.observation_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:12:14.735789+00:00
-- url     : https://prove2.me/theorems/08261e9c-8276-4379-a37f-7204a9c7ac87
-- title:
--   Observation 1 — splitting players preserves total balancedness
-- statement:
--   Let $(\tilde N,\tilde G)$ be generated from $(N,G)$ by splitting players with a splitting scheme $\Pi$, so that $G(S)=\tilde G(\bigcup_{i\in S}\Pi(i))$. If $(\tilde N,\tilde G)$ is totally balanced, then the constrained game $(\tilde N,\mathcal C,\tilde G)$ is totally balanced, and the game $(N,G)$ is totally balanced.
--
--   This is how total balancedness passes from the unit-speed games back up to the UCB games and the PMS game.
--
--   Differences from the source:
--   - encoding: a splitting scheme Π with (i) Π(i) ≠ ∅, (ii) disjointness, (iii) covering Ñ → a surjective father map π : Ñ → N, Π(i) = π⁻¹{i}; reason: (i)–(iii) say exactly that Π is the fibre partition of a surjection
--   - reading: a constrained game (Ñ, 𝒞, G̃) is totally balanced (term used, not defined) → ConstrainedTotallyBalanced: for every S ⊆ N some y : Ñ → ℝ has Σ_{Π(S)} y = G̃(Π(S)) and Σ_{Π(T)} y ≤ G̃(Π(T)) for all T ⊆ S; reason: Definition 3 applied to every constrained subgame on a feasible coalition Π(S), whose feasible subcoalitions are the Π(T), T ⊆ S
--   - generalization: cooperative games G̃ with G̃(∅) = 0 → any set function Gt : Finset Ñ → ℝ; reason: games with G̃(∅) = 0 are a special case; the argument does not use it
-- source:
--   Alon, Anily, The Basic Core of a Parallel Machines Scheduling Game, MSOM 25(6) (2023), doi:10.1287/msom.2021.0337, Observation 1, p.2237 (PDF p.6)

import Mathlib
import Definitions.Def_SplitPMSGame_IsCoreAlloc
import Definitions.Def_SplitPMSGame_ConstrainedTotallyBalanced

namespace SplitPMSGame

/-- **Observation 1** (Alon, Anily, *The Basic Core of a Parallel Machines Scheduling Game*, MSOM
25(6) (2023), p.2237): let `(Ñ, G̃)` be generated from `(N, G)` by splitting players with a
splitting scheme `Π` (Definition 1), so `G(S) = G̃(∪_{i∈S} Π(i))`. If `(Ñ, G̃)` is totally
balanced, then the constrained game `(Ñ, 𝒞, G̃)` is totally balanced, and the game `(N, G)` is
totally balanced.

**Formalization Note** The splitting scheme is the surjective father map `π : Ñ → N`
(`Π(i) = π⁻¹{i}`), and `(N, G)` is `splitGame π G̃`. `Gt` is `G̃`. -/
theorem observation_1 {Ñ N : Type*} [Fintype Ñ] [Fintype N] [DecidableEq N] (π : Ñ → N)
    (hπ : Function.Surjective π) (Gt : Finset Ñ → ℝ) (h : TotallyBalanced Gt) :
    ConstrainedTotallyBalanced π Gt ∧ TotallyBalanced (splitGame π Gt) := by sorry

end SplitPMSGame
