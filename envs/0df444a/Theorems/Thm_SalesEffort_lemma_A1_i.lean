-- Prove2me | Theorems.Thm_SalesEffort_lemma_A1_i
-- name    : SalesEffort.lemma_A1_i
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:15:34.581808+00:00
-- url     : https://prove2.me/theorems/65615932-6e2a-48c2-81e2-fc62f52c54d8
-- title:
--   Lemma A1(i), Online Appendix p.2 — increase propagates from $n-1$ to $n$ (corrected: $b+p>0$; at $t=0$ only for $n=2$, $b>0$)
-- statement:
--   Let $J$ solve the HJB system (2) with its boundary conditions on $t\ge0$, and assume $b+p>0$. Let $n\ge2$ and $0<z\le+\infty$. If
--   $$\frac{\partial\Delta_t(n-1)}{\partial t}\ge0\quad\text{for every }t\in[0,z],$$
--   then
--   $$\frac{\partial\Delta_t(n)}{\partial t}>0\quad\text{for every }t\in(0,z],$$
--   and also at $t=0$ when $n=2$ and $b>0$ (for $z=+\infty$, all ranges are over real $t$).
--
--   So if the marginal value of the $(n-1)$-st sale is nondecreasing in the time to go, the marginal value of the $n$-th is strictly increasing. This is the step that orders the cutoffs $\tau(n)$ in Theorem 1.
--
--   **Formalization Note** $z$ is an extended real; derivatives are derivatives within $[0,\infty)$, which exist at every $t\ge0$ for a solution of (2) (Inequality (OA.1)). The statement is indexed by $n+2$.
--
--   Differences from the source:
--   - correction: ∂∆_t(n)/∂t > 0 for any t ∈ [0, z] → > 0 for t ∈ (0, z], and at t = 0 when n = 2 and b > 0, under b + p > 0; reason: false at t = 0 for n ≥ 3, where ∆_0(n−1) = ∆_0(n) = 0 makes the derivative 0 (c(λ) = (λ−2)², λ̲ = 2, λ̄ = 10, b = 1, p = 2, n = 3, z = 1: ∆_t(2) is nondecreasing by Theorem 1(iii)); false for b = p = 0, where J ≡ 0 solves (2); at t = 0 and n = 2 the derivative is max{λb − c(λ)} − max{−c(λ)}, positive iff b > 0
--   - reading: Assumption 1(ii): c(λ) is invertible, and convex on [λ̲, λ̄] (with the proof's α = min c″ > 0, OA p.5) → c is continuous, injective and α-strongly convex on [λ̲, λ̄] for some α > 0; reason: the paper's 'regularity conditions specified in Assumption 1' (p.11) that make λ∗(t,n) unique; with convexity alone the arg max need not be unique (c(λ) = λ − 1 on [1, 3], p = 1)
--   - generalization: the proof uses c′ and c″ with min c″ = α > 0 on [λ̲, λ̄] → no derivative of c is assumed; reason: every C² cost with c″ ≥ α > 0 on [λ̲, λ̄] is α-strongly convex there, so the statement specializes to the source's
--   - reading: λ∗ = arg max{λ | λp − c(λ)} with λ∗ ∈ [λ̲, λ̄] (Assumption 1(iii)) → λ∗ is a maximizer of λp − c(λ) over [λ̲, λ̄]; reason: [λ̲, λ̄] is the feasible set of rates; the maximizer is unique by strong convexity, and an unconstrained arg max lying in [λ̲, λ̄] is this one
--   - encoding: J∗_t(n), the optimal expected profit, which is the solution of (2) with its boundary conditions, ∀t → any J solving (2) with both boundary conditions on t ∈ [0, ∞): derivative within [0, ∞) at every t ≥ 0 (one-sided at 0) equal to the attained maximum; reason: Theorem 1's proof uses only (2); Proposition 1 (a milestone) gives exactly one such solution on t ≥ 0; t is the time to go
--   - encoding: ∆_t(n) := J∗_t(n−1) − J∗_t(n), and J∗_t(−1) = J∗(0) + p (OA p.2) → marginal M J t n, equal to p at n = 0; reason: the paper's own convention ∆_t(0) = p
--   - encoding: 0 < z ≤ +∞, t ∈ [0, z], ∂/∂t → z : EReal with 0 < z, t real with 0 ≤ t and ↑t ≤ z, derivWithin on [0, ∞); reason: covers z = +∞; derivWithin is the true derivative because ∆_·(m) is differentiable within [0, ∞) for a solution of (2)
-- source:
--   Du, Hu & Wu, Sales Effort Management under All-or-Nothing Constraint, SSRN 3506499 (University of Toronto TSpace submitted manuscript), https://ssrn.com/abstract=3506499, Lemma A1(i), Online Appendix p.2 (PDF 36)

import Mathlib
import Definitions.Def_SalesEffort_Model

open Set Filter Topology

namespace SalesEffort

/-- **Lemma A1(i)** (corrected), Du, Hu & Wu, SSRN 3506499, Online Appendix p.2: "∀n ≥ 2 and
0 < z ≤ +∞, if ∂∆t(n−1)/∂t ≥ 0 for any t ∈ [0,z], then ∂∆t(n)/∂t > 0 for any t ∈ [0,z]".

**Formalization Note.**
1. Correction: the conclusion is stated under `b + p > 0`, on `t ∈ (0, z]`, and at `t = 0` only
   for `n = 2` with `b > 0`. At `t = 0` and `n ≥ 3`, `∆_0(n−1) = ∆_0(n) = 0`, so
   `∂∆_t(n)/∂t = 0` there; at `t = 0` and `n = 2` the derivative is
   `max_λ{λb − c(λ)} − max_λ{−c(λ)}`, which is `> 0` iff `b > 0`; and for `b = p = 0` the solution
   is `J ≡ 0`, so every derivative vanishes.
2. Indexed by `n + 2` (so `n + 2 ≥ 2`); `z : EReal` with `0 < z` covers `z = +∞`, and `t ∈ [0, z]`
   means `0 ≤ t` and `(t : EReal) ≤ z`.
3. `∂/∂t` is `derivWithin … (Ici 0) t`. For an HJB solution every `s ↦ ∆_s(m)` is differentiable
   within `[0, ∞)` at every `t ≥ 0` (Inequality (OA.1)), so `derivWithin` is the true derivative
   here, not a default value. -/
theorem lemma_A1_i (M : Model) (J : ℝ → ℕ → ℝ) (hJ : IsHJBSolution M J)
    (hbp : 0 < M.b + M.p) (n : ℕ) (z : EReal) (hz : 0 < z)
    (hprev : ∀ t : ℝ, 0 ≤ t → (t : EReal) ≤ z →
      0 ≤ derivWithin (fun s => marginal M J s (n + 1)) (Ici 0) t) :
    ∀ t : ℝ, 0 ≤ t → (t : EReal) ≤ z → (0 < t ∨ (n = 0 ∧ 0 < M.b)) →
      0 < derivWithin (fun s => marginal M J s (n + 2)) (Ici 0) t := by sorry

end SalesEffort
