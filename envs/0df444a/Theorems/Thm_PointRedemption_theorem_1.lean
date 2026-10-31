-- Prove2me | Theorems.Thm_PointRedemption_theorem_1
-- name    : PointRedemption.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:13:27.949765+00:00
-- url     : https://prove2.me/theorems/c1700d21-cf17-436f-aa14-7f0d0526a622
-- title:
--   Theorem 1, p. 13 — a unique optimal price satisfying the first-order condition (corrected: $\bar F(\Delta_{t-1}(y))>0$; $\bar\beta<1$ or $\bar F(R)>0$)
-- statement:
--   Consider the point-redemption pricing model and assume
--
--   1. A1: $F$ and $G$ have an increasing failure rate;
--   2. A2: for every $p\ge0$ with $\bar F(p)>0$, $\bar G(p/q)>0$ and $\dfrac{g(p/q)}{q\bar G(p/q)}\le\dfrac{f(p)}{\bar F(p)}$;
--   3. A3: $\dfrac{f(p)/\bar F(p)}{(\bar\beta g(p/q)/q)/(1-\bar\beta G(p/q))}$ is non-decreasing in $p$ on $\{p>0:\bar F(p)>0,\ g(p/q)>0\}$;
--   4. $f$ is differentiable at every $p>0$ with $\bar F(p)>0$ and $g$ at every $x>0$ with $\bar G(x)>0$.
--
--   Let $t\ge1$, $y\ge1$ with $\bar F(\Delta_{t-1}(y))>0$, and assume $\bar\beta<1$ or $\bar F(R)>0$. Then there is a unique optimal price $p^*_t(y)$, i.e. a unique $p\ge0$ with
--
--   $$J_t(p,y)=\max_{p'\ge0}J_t(p',y),$$
--
--   and it satisfies $p^*_t(y)>0$ and the first-order condition $\dfrac{\partial J_t}{\partial p}(p^*_t(y),y)=0$.
--
--   The theorem gives sufficient conditions under which the seller's revenue function is unimodal in price despite the substitution between cash and point purchases, so that the optimal price is characterized by its first-order condition.
--
--   **Formalization Note** The hypothesis $\bar F(\Delta_{t-1}(y))>0$ (the marginal value of inventory is below the top of the reservation-price support) is added; without it the set of optimal prices can be a half-line. So is "$\bar\beta<1$ or $\bar F(R)>0$": when every consumer is a reward consumer and $R$ lies beyond the top of $F$'s support, pricing out every cash buyer can be optimal, and again every price above that top is optimal. The first-order condition is stated as `HasDerivAt (J_t(·, y)) 0 p*`.
--
--   Differences from the source:
--   - correction: no condition on the marginal value Δ_{t−1}(y) → 0 < F̄(Δ_{t−1}(y)); reason: false as printed: F = U[0,1], G = U[0,2], q = 1, β̄ = 1, λ = 1/2, R = 10, (t, y) = (2, 1) satisfy A1–A3, Δ_1(1) = V_1(1) ≈ 1.262 ≥ 1, and every p ≥ 1 maximizes both J_2(·,1) on [0, ∞) and (3), so uniqueness, (22) and Proposition 1 fail
--   - correction: no condition relating R to the support of F → β̄ < 1 or F̄(R) > 0; reason: false as printed: F = U[0,100], G = U[0,10], q = 10, β̄ = 1, λ = 1/2, R = 250, t = y = 1 satisfy A1–A3 (A2 with equality, the A3 ratio constant 1), the regularity, β̄ > 0 and F̄(Δ_0(1)) = 1 > 0; with u = p/100, J_1(p,1)/λ = 100u(1−u)² + 250(u − u²/2) has derivative (1−u)(350 − 300u) > 0 on [0,1) and is constant for p ≥ 100, so every p ≥ 100 maximizes J_1(·,1); uniqueness fails, and p^c = 50 < R (g(5) = 1/10 > 0) with the maximizer p* = 300 > R contradicts (a). When β̄ < 1 the cash-only consumers make the derivative negative near the top of F's support; when F̄(R) > 0 it is negative on [max(R, p^c), top)
--   - reading: A2: f(p)/F̄(p) ≥ g(p/q)/Ḡ(p/q) for any p → for p ≥ 0 with F̄(p) > 0: Ḡ(p/q) > 0 and g(p/q)/(q Ḡ(p/q)) ≤ f(p)/F̄(p); reason: the hazard of the q-point worth qΘ carries the 1/q: the proof (App. p. 2) replaces f/F̄ by (g(p/q)/q)/Ḡ(p/q), Corollary 1 speaks of the "q point-worth distribution", and the paper's Figure 2 instance (q = 10) violates the printed form; where Ḡ(p/q) = 0 that hazard is +∞, so the inequality needs Ḡ(p/q) > 0
--   - generalization: A2 for any p → A2 required only for p ≥ 0 with F̄(p) > 0; reason: a weaker hypothesis: only prices p ≥ 0 enter (1), and where F̄(p) = 0 the paper's left side is +∞; every instance of the printed A2 satisfies it
--   - reading: A3: (f(p)/F̄(p))/(β̄g(p/q)/(1 − β̄G(p/q))) non-decreasing in p → (f(p)/F̄(p))/((β̄g(p/q)/q)/(1 − β̄G(p/q))) MonotoneOn {p | 0 < p, F̄(p) > 0, g(p/q) > 0}; reason: the ratio is a finite positive real exactly on that set; the constant factor 1/q (as in (21)) does not change monotonicity
--   - reading: densities f, g with no regularity stated, but f′ and g′ used in (8) → f differentiable at every p > 0 with F̄(p) > 0; g differentiable at every x > 0 with Ḡ(x) > 0; reason: the proof differentiates f and g at the prices in play; without it the first-order condition fails (F = U[0,3], G = 1.2 + Exp(1/3), q = 1, β̄ = 1, R = 0: the maximizer is the kink p = 1.2); the paper's uniform, exponential and truncated-normal examples satisfy it
--   - encoding: A1: F and G have an increasing failure rate → LariviereIGFR.Char.IsIFR for (μV, f) and (μΘ, g): f/F̄ and g/Ḡ weakly increasing on {cdf < 1}; reason: the standard IFR definition on the set where the hazard is finite
--   - encoding: "satisfies the first-order condition for J_t(p,y)" → 0 < p* and HasDerivAt (J_t(·, y)) 0 p*; reason: the first-order condition is the vanishing of the derivative at an interior price
--   - encoding: β̄(q) at the fixed q; t = 1, …, T periods with horizon T → βbar a number in [0,1] with β = 1 − βbar; t ≥ 1 counts periods to go, no horizon T; reason: the paper fixes q and writes β̄ for β̄(q) (p. 11); T only bounds t, so every t ≥ 1 is an instance of some horizon
--   - reading: R, the reimbursement, with no sign stated → R ≥ 0 (a field of the model); reason: R is revenue from the point issuer; Prop. 5(b) writes "any reimbursement rate R > 0"
-- source:
--   Chung–Ahn–Chun, Dynamic Pricing with Point Redemption, SSRN 3426903 (KAIST WP KCB-WP-2019-013); MSOM (2022), doi:10.1287/msom.2021.1067, Theorem 1, p. 13 (PDF 14); proof App. pp. 1–2 (PDF 36–37)

import Mathlib
import Definitions.Def_PointRedemption_Model

namespace PointRedemption

open MeasureTheory ProbabilityTheory

/-- **Theorem 1** (corrected), Chung–Ahn–Chun, *Dynamic Pricing with Point Redemption*,
SSRN 3426903; MSOM (2022), doi:10.1287/msom.2021.1067, p. 13 (PDF 14). Under A1, A2, A3 and the
regularity of the densities, for `t ≥ 1`, `y ≥ 1` with `F̄(Δ_{t−1}(y)) > 0`, and with `β̄ < 1` or
`F̄(R) > 0`, `J_t(·, y)` has a unique maximizer `p*_t(y)` on `[0, ∞)`; it is positive and
satisfies the first-order condition `∂J_t(p, y)/∂p = 0`.

**Formalization Note.** Correction: the hypothesis `F̄(Δ_{t−1}(y)) > 0` is added; without it the
maximizer set can be a whole half-line (`F = U[0,1]`, `G = U[0,2]`, `q = 1`, `β̄ = 1`, `λ = 1/2`,
`R = 10`, `(t, y) = (2, 1)`: every `p ≥ 1` is optimal). Correction: `β̄ < 1 ∨ F̄(R) > 0` is added;
when every consumer is a reward consumer and `R` lies beyond the top of `F`'s support, pricing out
all cash buyers can be optimal (`F = U[0,100]`, `G = U[0,10]`, `q = 10`, `β̄ = 1`, `λ = 1/2`,
`R = 250`, `t = y = 1`: `J_1(·, 1)` is increasing on `[0, 100]` and constant after, so every
`p ≥ 100` is optimal). A2 carries the `1/q` of the hazard of
`qΘ` and `Ḡ(p/q) > 0`; A3 is read on the set where its ratio is a finite positive real; the
densities are differentiable where the paper's `f′`, `g′` are used. -/
theorem theorem_1 (P : Params) (h1 : P.A1) (h2 : P.A2) (h3 : P.A3) (hreg : P.Regular)
    (t y : ℕ) (ht : 1 ≤ t) (hy : 1 ≤ y) (hΔ : 0 < P.Fbar (P.Δ (t - 1) y))
    (hR : P.βbar < 1 ∨ 0 < P.Fbar P.R) :
    (∃! p : ℝ, 0 ≤ p ∧ IsMaxOn (fun x => P.J t x y) (Set.Ici 0) p) ∧
      ∀ p : ℝ, 0 ≤ p → IsMaxOn (fun x => P.J t x y) (Set.Ici 0) p →
        0 < p ∧ HasDerivAt (fun x => P.J t x y) 0 p := by sorry

end PointRedemption
