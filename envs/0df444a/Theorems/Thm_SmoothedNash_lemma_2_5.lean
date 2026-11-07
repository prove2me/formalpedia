-- Prove2me | Theorems.Thm_SmoothedNash_lemma_2_5
-- name    : SmoothedNash.lemma_2_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:49:56.270196+00:00
-- url     : https://prove2.me/theorems/74a2b540-0279-4d96-9310-5874db62cb0c
-- title:
--   Lemma 2.5 — a center within $\rho_t$ of an exact equilibrium passes the level-$t$ test
-- statement:
--   Let $u$ be a game with payoffs in $[0, 1]$ and let $x^\star$ be an exact Nash equilibrium of $u$ with support profile $A$, that is, $A_i = \{a : x^\star_i(a) > 0\}$ for every player $i$. If $c \in K_A$ satisfies
--   $$
--   \|c - x^\star\|_1 \le \rho_t ,
--   $$
--   then $c$ passes the level-$t$ test.
--
--   This guarantees that the correct support guess never discards the centers near an equilibrium.
--
--   Differences from the source:
--   - encoding: x⋆ an exact Nash equilibrium (ε = 0 in the pure-deviation definition, p.6) → AGT.IsMixedNash u xs (no profitable deviation to any lottery); reason: for mixed profiles the two are equivalent (a lottery deviation is a convex combination of pure ones)
--   - encoding: A the support profile of x⋆ → a support profile A with A_i = {a : x⋆_i(a) > 0} (hypothesis hA); reason: the definition of the support profile
--   - encoding: games with payoffs u_i : [n]^m → [0, 1] (p.6) → real payoffs u with the hypothesis PayoffsIn01 u; reason: the range [0, 1] is part of the paper's game model and is stated as a hypothesis
--   - generalization: a game with m players, each with n actions (m, n ≥ 1 implicit) → any m, n ∈ ℕ, including 0; reason: the statement specializes to m, n ≥ 1; for m = 0 or n = 0 the instance is degenerate (the hypotheses are unsatisfiable or the claim is immediate)
--   - encoding: players [m] and actions [n], numbered from 1 → Fin m and Fin n, numbered from 0; reason: Lean indexing; same games
-- source:
--   Attias–Dagan–Daskalakis–Yao–Zampetakis, Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis, STOC 2027 submission (manuscript sha256 3f9ea37d…77a1ea53), Lemma 2.5, pp.16–17

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_SmoothedNash_Game
import Definitions.Def_SmoothedNash_PayoffsIn01
import Definitions.Def_SmoothedNash_SupportProfile
import Definitions.Def_SmoothedNash_InK
import Definitions.Def_SmoothedNash_l1
import Definitions.Def_SmoothedNash_rho
import Definitions.Def_SmoothedNash_PassesTest

namespace SmoothedNash

/-- **Lemma 2.5 (A center close to the exact equilibrium survives)** (Attias–Dagan–Daskalakis–Yao–Zampetakis, *Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis*, STOC 2027 submission manuscript (sha256 3f9ea37d…77a1ea53), pp.16–17). Let `x⋆` be
an exact Nash equilibrium of the realized game (payoffs in `[0, 1]`) with support profile `A`, i.e.
`A_i = {a : x⋆_i(a) > 0}`. If `c ∈ K_A` satisfies `‖c − x⋆‖_1 ≤ ρ_t`, then `c` passes the level-`t`
test.

**Formalization Note** "Exact Nash equilibrium" is the published `AGT.IsMixedNash` (no profitable
deviation to any lottery), which for mixed profiles is equivalent to the pure-deviation
`IsEpsNash u 0` of p.6. -/
theorem lemma_2_5 {m n : ℕ} (u : Game m n) (hu : PayoffsIn01 u) (xs : Fin m → Fin n → ℝ)
    (hxs : AGT.IsMixedNash (S := fun _ : Fin m => Fin n) u xs) (A : SupportProfile m n)
    (hA : ∀ i a, a ∈ A.1 i ↔ 0 < xs i a) (t : ℕ) (c : Fin m → Fin n → ℝ) (hc : InK A c)
    (hdist : l1 c xs ≤ rho m t) :
    PassesTest u A (2 * rho m t) c := by sorry

end SmoothedNash
