-- Prove2me | Theorems.Thm_WarrantyMatch_proposition_1
-- name    : WarrantyMatch.proposition_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:38:16.625988+00:00
-- url     : https://prove2.me/theorems/c7372756-4015-4fef-881c-ae73d480b483
-- title:
--   Proposition 1 — distribution-free bound $\frac{(1+a_r\epsilon)^2+b_r\epsilon^2}{4}\beta T_w$ for random assignment (corrected: tightness only for $\epsilon=0$ or $y=0$, with $(l+1)\epsilon\le 1$)
-- statement:
--   A wireless service provider replaces failed devices from an inventory of refurbished devices. Let $(D_u)_{u\in\mathbb Z}$ be the customer-warranty termination dates, $D_u$ being the date of a randomly chosen customer who files a claim in period $u$. Assume the standing model up to period $t$: the $D_u$, $u\le t$, are independent integer random variables, their laws drift by at most $\varepsilon$ per period in Kolmogorov–Smirnov distance,
--   $$
--   |P(D_{u+1}\le k)-P(D_u\le k)|\le\varepsilon\quad(u+1\le t,\ k\in\mathbb Z),\tag{6}
--   $$
--   and $D_u\le t+T_w$ almost surely for every $u\le t$, where $T_w\in\mathbb N$ is the warranty length. Let $l\in\mathbb N$ be the repair lead time, $\beta\ge0$ the cost per uncovered period, $d>0$ the demand and $y\ge0$ the inventory per period, and put
--   $$
--   a_r=l+\frac{y+d}{d},\qquad b_r=\frac{y(y+d)}{d^2}.
--   $$
--   Under random assignment the device given to a period-$t$ customer was returned $l+Z$ periods earlier, so its OEM termination date is $Y_t=D_{t-l-Z}$, where $Z$, the time in inventory, is a geometric number of trials with parameter $d/(y+d)$ (values $1,2,\dots$) independent of the dates. Then:
--
--   1. for every period $t$, with the cost $c_t(i,j)=\beta\,(j-\max(i,t))^+$ of (1),
--   $$
--   E[c_t(Y_t,D_t)]\le\frac{(1+a_r\varepsilon)^2+b_r\varepsilon^2}{4}\cdot\beta\cdot T_w ;
--   $$
--   2. for every horizon $T\ge1$, if the standing model holds up to every period $t=1,\dots,T$ and each period $t=1,\dots,T$ has its own such inventory time $Z_t$, independent of the dates, then the uncovered times $U^R_t=(D_t-\max(D_{t-l-Z_t},t))^+$ satisfy
--   $$
--   \frac1T\sum_{t=1}^T E[U^R_t]\le\frac{(1+a_r\varepsilon)^2+b_r\varepsilon^2}{4}\cdot T_w .
--   $$
--   3. if $\varepsilon\ge0$, $(l+1)\varepsilon\le1$ and ($\varepsilon=0$ or $y=0$), the bound of 1 is tight: for every $t$ some model of this form, on some probability space, attains it with equality.
--
--   The bound requires no knowledge of the termination-date distributions beyond their slow drift, and quantifies how much uncovered warranty time random assignment can cause; it is the benchmark against which the paper's sorting policies are compared.
--
--   **Formalization Note** Dates are integers and $t-l-Z$ is integer subtraction. The support clause is the bound at the current period that the paper's proof states (p.ec4), for customers and returned devices alike; it is implied by the sharper $D_u\le u+T_w$, and it admits stationary laws ($\varepsilon=0$), so the statement has content for every $\varepsilon\ge0$. The witness in clause 3 lives on its own probability space, and the conditions there are exactly those under which $(l+Z)\varepsilon\le1$ almost surely.
--
--   Differences from the source:
--   - correction: "This bound is tight, i.e., there is a distribution of D_t that achieves this bound" → the bound is attained when ε ≥ 0, (l + 1)ε ≤ 1 and (ε = 0 or y = 0) (clause 3), on a probability space of its own; reason: false for general parameters; at β = 1, T_w = 1, l = 0, d = 1, y = 0 (Z ≡ 1), ε = 2 the bound is 9/4, but the cost is at most T_w = 1 (constant dates D_u = t are admissible); more generally, for ε > 0, T_w > 0, β > 0, whenever (l + Z)ε > 1 has positive probability (always if y > 0) the conditional cost is at most βT_w, strictly below the conditional bound (1 + (l + Z)ε)²/4 · βT_w, so no distribution attains it; on the parameters kept, the two-point argument of p.ec5 works, with P(D_u = t) stepping by ε from (1 + (l + 1)ε)/2 at u = t − l − 1 to (1 − (l + 1)ε)/2 at u = t
--   - reading: D_t for t ∈ [1, T], independent → a family D_u indexed by all integers u ≤ t, mutually independent; reason: Y_t = D_{t−l−Z} reaches arbitrarily far back because Z is unbounded when y > 0
--   - reading: Z geometric with parameter d/(y + d), its dependence on the dates unstated → Z independent of (D_u)_{u ≤ t}; reason: the proof conditions on Z and applies Lemma EC.1 to the unconditional laws of D_t and D_{t−l−z}
--   - reading: geometric random variable → Z ∈ {1, 2, …} with P(Z = k + 1) = (1 − q)^k q; reason: the proof's E[Z] = (y + d)/d fixes the number-of-trials convention
--   - reading: warranty length T_w → hypothesis D_u ≤ t + T_w almost surely for every u ≤ t; reason: p.ec4, "at time t, customers and devices will have latest warranty termination date of t + Tw"; the sharper D_u ≤ u + T_w implies it
--   - reading: U^R_t the uncovered time under random assignment, one Z → U^R_t = (D_t − max(D_{t−l−Z_t}, t))⁺ with its own inventory time Z_t per period, each independent of the dates, and the model holding up to every t = 1, …, T; reason: p.13 defines the uncovered time as (D_t − max(Y_t, t))⁺, i.e. c_t with β = 1, and every period draws its own device
--   - encoding: (6) as a maximum over k = 1, …, m → every k ∈ ℤ; reason: same condition on [1, m]
--   - generalization: d, y the constant demand and inventory counts → real d > 0, y ≥ 0; reason: only q = d/(y + d) ∈ (0, 1] enters; integer counts are a special case
--   - generalization: customers in period u file with termination date at least u (p.8) → no lower bound on D_u; reason: the proof replaces D_t by max(D_t, t); families with the lower bound are a special case
--   - generalization: t ∈ [1, T] in the statement → every integer t in clause 1; reason: the proof uses no other property of t; [1, T] is a special case
-- source:
--   Calmon–Graves–Lemmens, Warranty Matching in a Consumer Electronics Closed-Loop Supply Chain, INSEAD WP 2020/03/TOM (SSRN 3357683), Proposition 1, p.13; model §4, eq. (6), p.12, and §4.1, p.13; proof §EC.2, pp.ec4–ec5

import Mathlib
import Definitions.Def_WarrantyMatch_Model

open MeasureTheory ProbabilityTheory

namespace WarrantyMatch

/-- **Proposition 1** (distribution-free bound for random assignment), tightness corrected.
Let the customer-warranty termination dates `D u` satisfy the standing model (`Admissible`:
independent, drift (6) with parameter `ε`, `D_u ≤ t + T_w`), let `l` be the lead time, `β ≥ 0`
the cost rate, `d > 0` the demand and `y ≥ 0` the inventory per period, and let
`a_r = l + (y + d)/d`, `b_r = y(y + d)/d²`.
1. For every period `t` and every geometric number of trials `Z` with parameter `d/(y + d)`,
   independent of the dates, the expected cost of assigning the device `Y_t = D_{t−l−Z}` satisfies
   `E[c_t(Y_t, D_t)] ≤ ((1 + a_r ε)² + b_r ε²)/4 · β · T_w`.
2. For every horizon `T ≥ 1`, if the model holds up to each `t = 1, …, T` and `Z_t` are
   such geometric times, each independent of the dates, then the uncovered times
   `U^R_t = (D_t − max(D_{t−l−Z_t}, t))⁺` satisfy
   `(1/T) ∑_{t=1}^T E[U^R_t] ≤ ((1 + a_r ε)² + b_r ε²)/4 · T_w`.
3. If `ε ≥ 0`, `(l + 1) ε ≤ 1` and (`ε = 0` or `y = 0`), the bound of 1 is tight: some model
   attains it with equality.
Calmon–Graves–Lemmens, *Warranty Matching in a Consumer Electronics Closed-Loop Supply Chain*,
INSEAD WP 2020/03/TOM (SSRN 3357683), Proposition 1, p.13; proof §EC.2, pp.ec4–ec5.

**Formalization Note** The printed claim "This bound is tight, i.e., there is a distribution of
`D_t` that achieves this bound", for all parameters, is false: conditionally on `Z = z` the cost
is at most `β T_w`, which is below `(1 + (l + z) ε)²/4 · β T_w` as soon as `(l + z) ε > 1`, and
this has positive probability unless `ε = 0` or (`y = 0` and `(l + 1) ε ≤ 1`). Clause 3 keeps
the claim on exactly those parameters, which are the ones the paper's two-point argument
(p.ec5) covers. `d, y` are reals, `T_w, l` naturals, dates integers, and `Z` takes values in
`{1, 2, …}`. The family is indexed by all integers `u ≤ t`; no lower bound `D_u ≥ u` is
assumed. The witness in clause 3 lives on its own probability space. -/
theorem proposition_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (D : ℤ → Ω → ℤ) (ε β d y : ℝ) (Tw l : ℕ) (hβ : 0 ≤ β) (hd : 0 < d) (hy : 0 ≤ y) :
    (∀ (t : ℤ) (Z : Ω → ℕ), Admissible P D ε Tw t → IsGeomTrials P Z (d / (y + d)) →
        IndepFun Z (fun ω (u : Set.Iic t) => D u ω) P →
        ∫ ω, cost β t (D (t - l - Z ω) ω) (D t ω) ∂P ≤
          ((1 + aR l y d * ε) ^ 2 + bR y d * ε ^ 2) / 4 * β * Tw) ∧
    (∀ (T : ℕ) (Z : ℤ → Ω → ℕ), 1 ≤ T →
        (∀ t ∈ Finset.Icc (1 : ℤ) T, Admissible P D ε Tw t) →
        (∀ t ∈ Finset.Icc (1 : ℤ) T, IsGeomTrials P (Z t) (d / (y + d))) →
        (∀ t ∈ Finset.Icc (1 : ℤ) T, IndepFun (Z t) (fun ω (u : Set.Iic t) => D u ω) P) →
        (1 / (T : ℝ)) * ∑ t ∈ Finset.Icc (1 : ℤ) T,
            ∫ ω, uncovered t (D (t - l - Z t ω) ω) (D t ω) ∂P ≤
          ((1 + aR l y d * ε) ^ 2 + bR y d * ε ^ 2) / 4 * Tw) ∧
    (∀ t : ℤ, 0 ≤ ε → ((l : ℝ) + 1) * ε ≤ 1 → (ε = 0 ∨ y = 0) →
      ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (_ : IsProbabilityMeasure P')
        (D' : ℤ → Ω' → ℤ) (Z' : Ω' → ℕ),
        Admissible P' D' ε Tw t ∧ IsGeomTrials P' Z' (d / (y + d)) ∧
        IndepFun Z' (fun ω (u : Set.Iic t) => D' u ω) P' ∧
        ∫ ω, cost β t (D' (t - l - Z' ω) ω) (D' t ω) ∂P' =
          ((1 + aR l y d * ε) ^ 2 + bR y d * ε ^ 2) / 4 * β * Tw) := by sorry

end WarrantyMatch
