-- Prove2me | Theorems.Thm_SalesEffort_lemma_A1_ii
-- name    : SalesEffort.lemma_A1_ii
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:15:41.203102+00:00
-- url     : https://prove2.me/theorems/ee8976a3-bd19-4453-8913-27d929845dcc
-- title:
--   Lemma A1(ii), Online Appendix p.2 — once $\Delta_t(n)$ stops increasing it never increases again (corrected: $z>0$ for $n\ge2$ unless $b=p=0$)
-- statement:
--   Let $J$ solve the HJB system (2) with its boundary conditions on $t\ge0$. Let $n\ge1$ and $z\ge0$, with $z>0$ when $n\ge2$ (unless $b=p=0$). If
--   $$\frac{\partial\Delta_t(n)}{\partial t}\Big|_{t=z}\le0,$$
--   then $\dfrac{\partial\Delta_t(n)}{\partial t}\le0$ for every $t>z$.
--
--   Together with the fact that $\Delta_t(n)$ approaches its limit $p$ from above when $b>p$, this gives the "first increase, then decrease" shape of Theorem 1(ii).
--
--   **Formalization Note** Derivatives are derivatives within $[0,\infty)$, which exist at every $t\ge0$ for a solution of (2).
--
--   Differences from the source:
--   - correction: ∀n ≥ 1, any z → z ≥ 0, and z > 0 when n ≥ 2 unless b = p = 0; reason: at z = 0 and n ≥ 3 the hypothesis always holds (derivative 0) while ∆_t(n) rises from ∆_0(n) = 0 (c(λ) = (λ−2)², λ̲ = 2, λ̄ = 10, b = 40, p = 2, n = 3); at n = 2, z = 0 the hypothesis forces b = 0, and p > 0 then makes ∆_t(2) increase; for b = p = 0, J ≡ 0 and z = 0 is kept
--   - reading: Assumption 1(ii): c(λ) is invertible, and convex on [λ̲, λ̄] (with the proof's α = min c″ > 0, OA p.5) → c is continuous, injective and α-strongly convex on [λ̲, λ̄] for some α > 0; reason: the paper's 'regularity conditions specified in Assumption 1' (p.11) that make λ∗(t,n) unique; with convexity alone the arg max need not be unique (c(λ) = λ − 1 on [1, 3], p = 1)
--   - generalization: the proof uses c′ and c″ with min c″ = α > 0 on [λ̲, λ̄] → no derivative of c is assumed; reason: every C² cost with c″ ≥ α > 0 on [λ̲, λ̄] is α-strongly convex there, so the statement specializes to the source's
--   - reading: λ∗ = arg max{λ | λp − c(λ)} with λ∗ ∈ [λ̲, λ̄] (Assumption 1(iii)) → λ∗ is a maximizer of λp − c(λ) over [λ̲, λ̄]; reason: [λ̲, λ̄] is the feasible set of rates; the maximizer is unique by strong convexity, and an unconstrained arg max lying in [λ̲, λ̄] is this one
--   - encoding: J∗_t(n), the optimal expected profit, which is the solution of (2) with its boundary conditions, ∀t → any J solving (2) with both boundary conditions on t ∈ [0, ∞): derivative within [0, ∞) at every t ≥ 0 (one-sided at 0) equal to the attained maximum; reason: Theorem 1's proof uses only (2); Proposition 1 (a milestone) gives exactly one such solution on t ≥ 0; t is the time to go
--   - encoding: ∆_t(n) := J∗_t(n−1) − J∗_t(n), and J∗_t(−1) = J∗(0) + p (OA p.2) → marginal M J t n, equal to p at n = 0; reason: the paper's own convention ∆_t(0) = p
--   - encoding: ∂∆_t(n)/∂t → derivWithin on [0, ∞); reason: the true derivative, since ∆_·(n) is differentiable within [0, ∞) for a solution of (2)
-- source:
--   Du, Hu & Wu, Sales Effort Management under All-or-Nothing Constraint, SSRN 3506499 (University of Toronto TSpace submitted manuscript), https://ssrn.com/abstract=3506499, Lemma A1(ii), Online Appendix p.2 (PDF 36)

import Mathlib
import Definitions.Def_SalesEffort_Model

open Set Filter Topology

namespace SalesEffort

/-- **Lemma A1(ii)** (corrected), Du, Hu & Wu, SSRN 3506499, Online Appendix p.2: "∀n ≥ 1, if
∂∆t(n)/∂t |_{t=z} ≤ 0, then ∂∆t(n)/∂t ≤ 0 for any t > z".

**Formalization Note.**
1. Correction: for `n ≥ 2` the start point must satisfy `z > 0`, unless `b = p = 0` (then `J ≡ 0`
   and the printed claim holds at `z = 0` too); for `n = 1`, `z ≥ 0` as printed.
   At `z = 0` and `n ≥ 3` the hypothesis always holds (`∆_0(n−1) = ∆_0(n) = 0` give derivative `0`),
   while `∆_t(n)` rises from `∆_0(n) = 0`; e.g. `c(λ) = (λ−2)²`, `λ̲ = 2`, `λ̄ = 10`, `b = 40`, `p = 2`,
   `n = 3`. For `n = 2`, `z = 0` the hypothesis forces `b = 0`, and then `p > 0` makes `∆_t(2)` increase.
2. `z` ranges over `[0, ∞)`, the domain of the time to go.
3. `∂/∂t` is `derivWithin … (Ici 0) t`, the true derivative for an HJB solution (Inequality (OA.1)). -/
theorem lemma_A1_ii (M : Model) (J : ℝ → ℕ → ℝ) (hJ : IsHJBSolution M J)
    (n : ℕ) (hn : 1 ≤ n) (z : ℝ) (hz : 0 ≤ z) (hz2 : 2 ≤ n → 0 < z ∨ M.b + M.p = 0)
    (hzd : derivWithin (fun s => marginal M J s n) (Ici 0) z ≤ 0) :
    ∀ t : ℝ, z < t → derivWithin (fun s => marginal M J s n) (Ici 0) t ≤ 0 := by sorry

end SalesEffort
