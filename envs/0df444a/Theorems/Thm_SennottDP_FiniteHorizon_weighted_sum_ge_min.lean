-- Prove2me | Theorems.Thm_SennottDP_FiniteHorizon_weighted_sum_ge_min
-- name    : SennottDP.FiniteHorizon.weighted_sum_ge_min
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T06:22:35.097116+00:00
-- url     : https://prove2.me/theorems/b5246f2d-f4a9-47ae-8606-d68b5c118907
-- title:
--   Proposition A.1.1 — a probability average of $u$ is at least $\min u$, with equality iff concentrated on the minimizers
-- statement:
--   Let $A$ be a finite nonempty set, $(q(a))_{a \in A}$ a probability distribution on $A$ ($q(a) \ge 0$, $\sum_{a} q(a) = 1$) and $u : A \to (-\infty, \infty]$. Then
--   $$
--   \sum_{a \in A} q(a)\, u(a) \ \ge\ \min_{a \in A} u(a),
--   $$
--   and equality holds if and only if $q$ is concentrated on $B = \{ b \in A : u(b) = \min_{a \in A} u(a) \}$, that is, $q(a) = 0$ for every $a \in A - B$.
--
--   This elementary fact is the step of the finite horizon optimality equation that identifies optimal randomized decisions: a randomization can only match the minimum by putting all its weight on minimizing actions.
--
--   **Formalization Note** $u$ takes values in the extended reals `EReal` and is assumed to avoid $-\infty$; the convention $0 \cdot \infty = 0$ is that of `EReal`.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 270, Proposition A.1.1

import Mathlib

namespace SennottDP.FiniteHorizon

/-- Proposition A.1.1 (Sennott, p. 270). Let `(q(a))_{a ∈ A}` be a probability distribution on
the finite nonempty set `A` and `u : A → (−∞, ∞]`. Then `∑_{a ∈ A} q(a) u(a) ≥ min_{a ∈ A} u(a)`,
with equality iff `q` is concentrated on `B = {b ∈ A | u(b) = min_{a ∈ A} u(a)}`, i.e. `q(a) = 0`
for `a ∈ A − B`. Values of `u` are extended reals different from `−∞` (`0 · ∞ = 0`). -/
theorem weighted_sum_ge_min {ι : Type} (A : Finset ι) (hA : A.Nonempty) (q : ι → ℝ)
    (hq_nonneg : ∀ a ∈ A, 0 ≤ q a) (hq_sum : ∑ a ∈ A, q a = 1)
    (u : ι → EReal) (hu : ∀ a ∈ A, u a ≠ ⊥) :
    A.inf' hA u ≤ ∑ a ∈ A, ((q a : ℝ) : EReal) * u a ∧
    (∑ a ∈ A, ((q a : ℝ) : EReal) * u a = A.inf' hA u ↔
      ∀ a ∈ A, u a ≠ A.inf' hA u → q a = 0) := by sorry

end SennottDP.FiniteHorizon
