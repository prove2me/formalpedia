-- Prove2me | Theorems.Thm_SmoothedNash_lemma_2_9
-- name    : SmoothedNash.lemma_2_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:49:51.63023+00:00
-- url     : https://prove2.me/theorems/484ae34f-f872-4f3f-a807-ad0d2baf0149
-- title:
--   Lemma 2.9 — stability: $x \in E_A(\tau)$, $y \in K_A$, $\|x-y\|_1 \le \delta$ give $y \in E_A(\tau + 2\delta)$
-- statement:
--   Let $u$ be a game with payoffs in $[0, 1]$ and $A$ a support profile. If $x \in E_A(\tau)$, $y \in K_A$ and $\|x - y\|_1 \le \delta$, then
--   $$
--   y \in E_A(\tau + 2\delta).
--   $$
--   Every child of a passing center therefore lies in a slightly relaxed survival region, which is how Lemma 2.10 bounds the frontiers by the survival probabilities of fixed grid points.
--
--   Differences from the source:
--   - generalization: τ ≥ 0 (E_A(τ) is defined for τ ≥ 0) and δ the bound on ‖x − y‖₁ → any real τ and δ; reason: for τ < 0 or δ < 0 the hypotheses cannot hold (an anchor compares with itself; ‖x − y‖₁ ≥ 0), so the statement specializes to the source's
--   - encoding: games with payoffs u_i : [n]^m → [0, 1] (p.6) → real payoffs u with the hypothesis PayoffsIn01 u; reason: the range [0, 1] is part of the paper's game model and is stated as a hypothesis
--   - generalization: a game with m players, each with n actions (m, n ≥ 1 implicit) → any m, n ∈ ℕ, including 0; reason: the statement specializes to m, n ≥ 1; for m = 0 or n = 0 the instance is degenerate (the hypotheses are unsatisfiable or the claim is immediate)
--   - encoding: players [m] and actions [n], numbered from 1 → Fin m and Fin n, numbered from 0; reason: Lean indexing; same games
-- source:
--   Attias–Dagan–Daskalakis–Yao–Zampetakis, Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis, STOC 2027 submission (manuscript sha256 3f9ea37d…77a1ea53), Lemma 2.9, p.18

import Mathlib
import Definitions.Def_SmoothedNash_Game
import Definitions.Def_SmoothedNash_PayoffsIn01
import Definitions.Def_SmoothedNash_SupportProfile
import Definitions.Def_SmoothedNash_InK
import Definitions.Def_SmoothedNash_l1
import Definitions.Def_SmoothedNash_PassesTest

namespace SmoothedNash

/-- **Lemma 2.9 (Stability of the relaxed survival region)** (Attias–Dagan–Daskalakis–Yao–Zampetakis, *Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis*, STOC 2027 submission manuscript (sha256 3f9ea37d…77a1ea53), p.18). For a game with payoffs in
`[0, 1]`: if `x ∈ E_A(τ)`, `y ∈ K_A` and `‖x − y‖_1 ≤ δ`, then `y ∈ E_A(τ + 2δ)`. -/
theorem lemma_2_9 {m n : ℕ} (u : Game m n) (hu : PayoffsIn01 u) (A : SupportProfile m n)
    (τ δ : ℝ) (x y : Fin m → Fin n → ℝ) (hx : InK A x) (hpass : PassesTest u A τ x)
    (hy : InK A y) (hxy : l1 x y ≤ δ) :
    PassesTest u A (τ + 2 * δ) y := by sorry

end SmoothedNash
