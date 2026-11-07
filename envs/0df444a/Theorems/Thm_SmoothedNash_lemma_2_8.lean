-- Prove2me | Theorems.Thm_SmoothedNash_lemma_2_8
-- name    : SmoothedNash.lemma_2_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:50:37.352423+00:00
-- url     : https://prove2.me/theorems/83a8cf58-c6f1-4c04-b212-9612a752d47b
-- title:
--   Lemma 2.8 — $P[x \in E_A(\tau)] \le M^{mn}(2\tau)^R$ for every fixed $x \in K_A$, $\tau \ge 0$
-- statement:
--   Let $G$ be a random game on a probability space $(\Omega, \mathcal F, P)$ with measurable payoffs, satisfying Assumption 1.18 with constant $M \ge 1$. Fix a support profile $A$ with $R = \sum_i (|A_i| - 1)$. For every fixed $x \in K_A$ and every $\tau \ge 0$,
--   $$
--   P\bigl[x \in E_A(\tau)\bigr] \le M^{mn} (2\tau)^R ,
--   $$
--   where $x \in E_A(\tau)$ means that $x$ passes the test with tolerance $\tau$ for the realized game.
--
--   The probability that a fixed point survives a test of tolerance $\tau$ is thus polynomially small in $\tau$, with exponent the dimension $R$; this is the source of the smoothed-analysis speed-up.
--
--   Differences from the source:
--   - encoding: a random (realized) game satisfying Assumption 1.18 → a probability space (Ω, P), a random game G with measurable payoffs, and BoundedDensity P G M; reason: measurability is implicit in "random game"; the density bound is the equivalent measure inequality of BoundedDensity
--   - generalization: games with payoffs u_i : [n]^m → [0, 1] (p.6) → no range hypothesis on the realized games G ω; reason: BoundedDensity already forces U(x) ∈ [0, 1]^{mn} almost surely; the statement specializes to games with payoffs in [0, 1]
--   - generalization: a game with m players, each with n actions (m, n ≥ 1 implicit) → any m, n ∈ ℕ, including 0; reason: the statement specializes to m, n ≥ 1; for m = 0 or n = 0 the instance is degenerate (the hypotheses are unsatisfiable or the claim is immediate)
--   - encoding: players [m] and actions [n], numbered from 1 → Fin m and Fin n, numbered from 0; reason: Lean indexing; same games
-- source:
--   Attias–Dagan–Daskalakis–Yao–Zampetakis, Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis, STOC 2027 submission (manuscript sha256 3f9ea37d…77a1ea53), Lemma 2.8, p.18

import Mathlib
import Definitions.Def_SmoothedNash_Game
import Definitions.Def_SmoothedNash_BoundedDensity
import Definitions.Def_SmoothedNash_SupportProfile
import Definitions.Def_SmoothedNash_R
import Definitions.Def_SmoothedNash_InK
import Definitions.Def_SmoothedNash_PassesTest
open MeasureTheory
open scoped ENNReal

namespace SmoothedNash

/-- **Lemma 2.8 (Probability of passing the relaxed survival test)** (Attias–Dagan–Daskalakis–Yao–Zampetakis, *Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis*, STOC 2027 submission manuscript (sha256 3f9ea37d…77a1ea53), p.18). Under
Assumption 1.18, for every fixed `x ∈ K_A` and every `τ ≥ 0`, `P[x ∈ E_A(τ)] ≤ M^{mn} (2τ)^R`.

**Formalization Note** `(Ω, P)` is a probability space and `G` a random game whose payoffs are
measurable; `x ∈ E_A(τ)` for the realized game `G ω` is `PassesTest (G ω) A τ x` (with `x ∈ K_A`
fixed). -/
theorem lemma_2_8 {m n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (G : Ω → Game m n) (hG : ∀ i s, Measurable fun ω => G ω i s)
    (M : ℝ) (hM : BoundedDensity P G M) (A : SupportProfile m n) (x : Fin m → Fin n → ℝ)
    (hx : InK A x) (τ : ℝ) (hτ : 0 ≤ τ) :
    P {ω | PassesTest (G ω) A τ x} ≤ ENNReal.ofReal (M ^ (m * n) * (2 * τ) ^ R A) := by sorry

end SmoothedNash
