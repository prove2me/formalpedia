-- Prove2me | Theorems.Thm_WarrantyMatch_conditional_bound
-- name    : WarrantyMatch.conditional_bound
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:38:12.442513+00:00
-- url     : https://prove2.me/theorems/549c38d0-af08-4f09-933c-6611edc5bb7b
-- title:
--   §EC.2 — $E[f(D_t-\max(D_{t-l-Z},t))]\le\frac{E[(1+(l+Z)\epsilon)^2]}{4}f(T_w)$
-- statement:
--   Let $f:\mathbb R\to\mathbb R$ be convex and nondecreasing with $f(x)=0$ for $x\le0$. Let $(D_u)_{u\in\mathbb Z}$ be an admissible family of customer-warranty termination dates up to period $t$: the $D_u$, $u\le t$, are independent integer random variables, they satisfy the drift condition (6) with parameter $\varepsilon$, and $D_u\le t+T_w$ almost surely for every $u\le t$. Let $l\in\mathbb N$ be the lead time and let $Z$ be a geometric number of trials with parameter $d/(y+d)$, $d>0$, $y\ge0$ (so $P(Z=k)=\frac{d}{y+d}\bigl(\frac{y}{y+d}\bigr)^{k-1}$, $k\ge1$), independent of $(D_u)_{u\le t}$. Then $(1+(l+Z)\varepsilon)^2$ is integrable and
--   $$
--   E\bigl[f\bigl(D_t-\max(D_{t-l-Z},t)\bigr)\bigr]\le\frac{E\bigl[(1+(l+Z)\varepsilon)^2\bigr]}{4}\,f(T_w).
--   $$
--
--   This is the step of the proof of Proposition 1 that conditions on the inventory time $Z$ and applies Lemma EC.1 with KS distance $(l+Z)\varepsilon$ (from (EC.3)) on the window $[t,t+T_w]$; it holds for every convex nondecreasing cost $f$ vanishing on $(-\infty,0]$, not only for the uncovered time.
--
--   **Formalization Note** The argument of $f$ is computed in $\mathbb Z$ and cast to $\mathbb R$. The integrability clause guarantees that the expectation on the right is the true one and not the value $0$ that Lean assigns to the integral of a non-integrable function.
--
--   Differences from the source:
--   - reading: D_t for t ∈ [1, T], independent → a family D_u indexed by all integers u ≤ t, mutually independent; reason: D_{t−l−Z} reaches arbitrarily far back because Z is unbounded when y > 0
--   - reading: Z geometric with parameter d/(y + d), its dependence on the dates unstated → Z independent of (D_u)_{u ≤ t}; reason: the proof conditions on Z and applies Lemma EC.1 to the unconditional laws of D_t and D_{t−l−z}
--   - reading: geometric random variable → Z ∈ {1, 2, …} with P(Z = k + 1) = (1 − q)^k q; reason: the proof's E[Z] = (y + d)/d fixes the number-of-trials convention
--   - reading: warranty length T_w (WLOG support at most [t, t + T_w]) → hypothesis D_u ≤ t + T_w almost surely for every u ≤ t; reason: p.ec4, "at time t, customers and devices will have latest warranty termination date of t + Tw"; the sharper D_u ≤ u + T_w implies it
--   - encoding: (6) as a maximum over k = 1, …, m → every k ∈ ℤ; reason: same condition on [1, m]
--   - encoding: the chain E[f] = E_Z[E[f | Z]] ≤ E_Z[…] = E[(1 + (l + Z)ε)²]/4 · f(T_w) → the inequality between its first and last members, plus integrability of (1 + (l + Z)ε)²; reason: the middle members are the proof's conditioning; integrability rules out Lean's junk value 0
--   - generalization: d, y the constant demand and inventory counts → real d > 0, y ≥ 0; reason: only q = d/(y + d) ∈ (0, 1] enters; integer counts are a special case
--   - generalization: customers in period u file with termination date at least u (p.8) → no lower bound on D_u; reason: the proof replaces D_t by max(D_t, t); families with the lower bound are a special case
-- source:
--   Calmon–Graves–Lemmens, Warranty Matching in a Consumer Electronics Closed-Loop Supply Chain, INSEAD WP 2020/03/TOM (SSRN 3357683), §EC.2, proof of Proposition 1, display after "we use Lemma EC.1 to obtain", p.ec4

import Mathlib
import Definitions.Def_WarrantyMatch_Model

open MeasureTheory ProbabilityTheory

namespace WarrantyMatch

/-- **§EC.2, proof of Proposition 1, conditioning display.** Let `f : ℝ → ℝ` be convex and
nondecreasing with `f x = 0` for `x ≤ 0`. Let the termination dates `D u` satisfy the standing
model up to period `t` (`Admissible`: independent, drift (6), `D_u ≤ t + T_w`), let `l` be the
lead time, and let `Z` be a geometric number of trials with parameter `d/(y + d)`
(`d > 0`, `y ≥ 0`), independent of the dates. Then `(1 + (l + Z)ε)²` is integrable and
`E[f(D_t − max(D_{t−l−Z}, t))] ≤ E[(1 + (l + Z)ε)²]/4 · f(T_w)`.
Calmon–Graves–Lemmens, *Warranty Matching in a Consumer Electronics Closed-Loop Supply Chain*,
INSEAD WP 2020/03/TOM (SSRN 3357683), §EC.2, proof of Proposition 1, display after "we use Lemma EC.1 to obtain", p.ec4.

**Formalization Note** The cost argument `D_t − max(D_{t−l−Z}, t)` is computed in `ℤ` and cast
to `ℝ`. `Z` is independent of the whole family `(D u)_{u ≤ t}`. The integrability clause rules
out a junk value `0` for the integral on the right. -/
theorem conditional_bound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (D : ℤ → Ω → ℤ) (Z : Ω → ℕ) (f : ℝ → ℝ) (ε d y : ℝ) (Tw l : ℕ) (t : ℤ)
    (hd : 0 < d) (hy : 0 ≤ y)
    (hconv : ConvexOn ℝ Set.univ f) (hmono : Monotone f) (hf0 : ∀ x ≤ 0, f x = 0)
    (hD : Admissible P D ε Tw t) (hZ : IsGeomTrials P Z (d / (y + d)))
    (hind : IndepFun Z (fun ω (u : Set.Iic t) => D u ω) P) :
    Integrable (fun ω => (1 + ((l : ℝ) + Z ω) * ε) ^ 2) P ∧
    ∫ ω, f (((D t ω - max (D (t - l - Z ω) ω) t : ℤ) : ℝ)) ∂P ≤
      (∫ ω, (1 + ((l : ℝ) + Z ω) * ε) ^ 2 ∂P) / 4 * f (Tw : ℝ) := by sorry

end WarrantyMatch
