-- Prove2me | Theorems.Thm_PointRedemption_proposition_1
-- name    : PointRedemption.proposition_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:13:36.779589+00:00
-- url     : https://prove2.me/theorems/58baf84a-5f69-4075-9d35-ed4596fe2e10
-- title:
--   Proposition 1, pp. 14–15 — the optimal price lies strictly between the blackout price and R (corrected: $\bar F(\Delta_{t-1}(y))>0$, $\bar\beta>0$, $g(p^c/q)>0$; (a): $\bar\beta<1$ or $\bar F(R)>0$)
-- statement:
--   Consider the point-redemption pricing model under the assumptions A1–A3 of Theorem 1 and the regularity of the densities (as in Theorem 1), with $\bar\beta>0$. Let $y\ge1$ units remain with $t\ge1$ periods to go, and assume $\bar F(\Delta_{t-1}(y))>0$. Then:
--
--   1. the objective $J_t(\cdot,y)$ of (1) has a maximizer $p^*_t(y)$ on $[0,\infty)$, and the blackout problem (3) has a maximizer $p^c_t(y)$ on $\mathbb R$;
--   2. for every maximizer $p^*=p^*_t(y)$ of (1) and every maximizer $p^c=p^c_t(y)$ of (3) with $g(p^c/q)>0$:
--      - (a) if the reimbursement rate is higher than the blackout price, $p^c<R$, and $\bar\beta<1$ or $\bar F(R)>0$, the optimal price tilts upward to it: $$p^c<p^*<R;$$
--      - (b) if the reimbursement rate is lower than the blackout price, $R<p^c$, the optimal price tilts downward to it: $$R<p^*<p^c.$$
--
--   Accepting points therefore pulls the optimal price strictly toward the reimbursement rate: point redemption raises the price when a reward sale is worth more than a cash sale at the blackout price, and lowers it otherwise.
--
--   **Formalization Note** The optimal and blackout prices are quantified maximizers (`IsMaxOn` on $[0,\infty)$ and on $\mathbb R$), never closed forms or roots of a first-order condition, and the existence of both is part of the conclusion. The hypotheses $\bar F(\Delta_{t-1}(y))>0$, $\bar\beta>0$ and $g(p^c/q)>0$ are added: without the first the maximizer sets can be half-lines, and without the other two the point channel is inactive at $p^c$ and $p^*=p^c$. In case (a), "$\bar\beta<1$ or $\bar F(R)>0$" is added: when every consumer is a reward consumer and $R$ lies beyond the top of $F$'s support, every price above that top can be optimal, including prices above $R$. In case (b) it holds automatically, since $R<p^c$ and $\bar F(p^c)>0$.
--
--   Differences from the source:
--   - correction: no condition on the marginal value Δ_{t−1}(y) → 0 < F̄(Δ_{t−1}(y)); reason: false as printed: F = U[0,1], G = U[0,2], q = 1, β̄ = 1, λ = 1/2, R = 10, (t, y) = (2, 1) satisfy A1–A3, Δ_1(1) = V_1(1) ≈ 1.262 ≥ 1, and every p ≥ 1 maximizes both J_2(·,1) on [0, ∞) and (3), so uniqueness, (22) and Proposition 1 fail
--   - correction: no condition on β̄ or on G at the blackout price → 0 < β̄, and the conclusion for every p^c with g(p^c/q) > 0; reason: false as printed: F = U[0,2], G = 3 + Gamma(3,1), q = 1, β̄ = 0.7, λ = 1/2, R = 1.5, t = y = 1 satisfy A1–A3 and F̄(Δ) = 1 > 0, but no consumer ever redeems (θ ≥ 3 > v), so p* = p^c = 1 < R, contradicting (a); β̄ = 0 fails the same way
--   - correction: no condition relating R to the support of F → in case (a), β̄ < 1 or F̄(R) > 0 (in case (b) F̄(R) ≥ F̄(p^c) > 0 holds automatically); reason: false as printed: F = U[0,100], G = U[0,10], q = 10, β̄ = 1, λ = 1/2, R = 250, t = y = 1 satisfy A1–A3 (A2 with equality, the A3 ratio constant 1), the regularity, β̄ > 0 and F̄(Δ_0(1)) = 1 > 0; with u = p/100, J_1(p,1)/λ = 100u(1−u)² + 250(u − u²/2) has derivative (1−u)(350 − 300u) > 0 on [0,1) and is constant for p ≥ 100, so every p ≥ 100 maximizes J_1(·,1); uniqueness fails, and p^c = 50 < R (g(5) = 1/10 > 0) with the maximizer p* = 300 > R contradicts (a). When β̄ < 1 the cash-only consumers make the derivative negative near the top of F's support; when F̄(R) > 0 it is negative on [max(R, p^c), top)
--   - reading: A2: f(p)/F̄(p) ≥ g(p/q)/Ḡ(p/q) for any p → for p ≥ 0 with F̄(p) > 0: Ḡ(p/q) > 0 and g(p/q)/(q Ḡ(p/q)) ≤ f(p)/F̄(p); reason: the hazard of the q-point worth qΘ carries the 1/q: the proof (App. p. 2) replaces f/F̄ by (g(p/q)/q)/Ḡ(p/q), Corollary 1 speaks of the "q point-worth distribution", and the paper's Figure 2 instance (q = 10) violates the printed form; where Ḡ(p/q) = 0 that hazard is +∞, so the inequality needs Ḡ(p/q) > 0
--   - generalization: A2 for any p → A2 required only for p ≥ 0 with F̄(p) > 0; reason: a weaker hypothesis: only prices p ≥ 0 enter (1), and where F̄(p) = 0 the paper's left side is +∞; every instance of the printed A2 satisfies it
--   - reading: A3: (f(p)/F̄(p))/(β̄g(p/q)/(1 − β̄G(p/q))) non-decreasing in p → (f(p)/F̄(p))/((β̄g(p/q)/q)/(1 − β̄G(p/q))) MonotoneOn {p | 0 < p, F̄(p) > 0, g(p/q) > 0}; reason: the ratio is a finite positive real exactly on that set; the constant factor 1/q (as in (21)) does not change monotonicity
--   - reading: densities f, g with no regularity stated, but f′ and g′ used in (8) → f differentiable at every p > 0 with F̄(p) > 0; g differentiable at every x > 0 with Ḡ(x) > 0; reason: the proof differentiates f and g at the prices in play; without it the first-order condition fails (F = U[0,3], G = 1.2 + Exp(1/3), q = 1, β̄ = 1, R = 0: the maximizer is the kink p = 1.2); the paper's uniform, exponential and truncated-normal examples satisfy it
--   - encoding: A1: F and G have an increasing failure rate → LariviereIGFR.Char.IsIFR for (μV, f) and (μΘ, g): f/F̄ and g/Ḡ weakly increasing on {cdf < 1}; reason: the standard IFR definition on the set where the hazard is finite
--   - generalization: "the optimal price p*_t(y)" and "the blackout price p^c_t(y)" (unique by Theorem 1 and (3)) → existence of both maximizers, and (a), (b) for every maximizer p* on [0, ∞) and every maximizer p^c on ℝ; reason: the conclusion for all maximizers specializes to the unique ones; existence is stated so that the universal statement is not vacuous
--   - encoding: (3): max_p over p as printed → IsMaxOn over Set.univ (all real p); reason: as printed; (1) itself restricts to p ≥ 0 (Set.Ici 0)
--   - encoding: β̄(q) at the fixed q; t = 1, …, T periods with horizon T → βbar a number in [0,1] with β = 1 − βbar; t ≥ 1 counts periods to go, no horizon T; reason: the paper fixes q and writes β̄ for β̄(q) (p. 11); T only bounds t, so every t ≥ 1 is an instance of some horizon
--   - reading: R, the reimbursement, with no sign stated → R ≥ 0 (a field of the model); reason: R is revenue from the point issuer; Prop. 5(b) writes "any reimbursement rate R > 0"
-- source:
--   Chung–Ahn–Chun, Dynamic Pricing with Point Redemption, SSRN 3426903 (KAIST WP KCB-WP-2019-013); MSOM (2022), doi:10.1287/msom.2021.1067, Proposition 1, pp. 14–15 (PDF 15–16); standing assumptions of Theorem 1, p. 13 (PDF 14); proof App. p. 5 (PDF 40)

import Mathlib
import Definitions.Def_PointRedemption_Model

namespace PointRedemption

open MeasureTheory ProbabilityTheory

/-- **Proposition 1** (corrected), Chung–Ahn–Chun, *Dynamic Pricing with Point Redemption*,
SSRN 3426903; MSOM (2022), doi:10.1287/msom.2021.1067, pp. 14–15 (PDF 15–16). Assume A1, A2, A3
of Theorem 1, regular densities and `β̄ > 0`. Given `y ≥ 1` units and `t ≥ 1` periods to go with
`F̄(Δ_{t−1}(y)) > 0`:
1. `J_t(·, y)` has a maximizer `p*_t(y)` on `[0, ∞)` and the blackout problem (3) has a
   maximizer `p^c_t(y)` on `ℝ`;
2. for every such `p*` and every such `p^c` with `g(p^c/q) > 0`:
   (a) if `p^c < R`, and `β̄ < 1` or `F̄(R) > 0`, then `p^c < p* < R`;
   (b) if `R < p^c` then `R < p* < p^c`.

**Formalization Note.** Corrections: `F̄(Δ_{t−1}(y)) > 0` (otherwise the maximizer sets of (1)
and (3) can both be `[1, ∞)`: `F = U[0,1]`, `G = U[0,2]`, `q = 1`, `β̄ = 1`, `λ = 1/2`, `R = 10`,
`(t, y) = (2, 1)`), and `β̄ > 0`, `g(p^c/q) > 0` (otherwise the reward channel is inactive at
`p^c` and `p* = p^c`: `F = U[0,2]`, `G = 3 + Gamma(3,1)`, `q = 1`, `β̄ = 0.7`, `λ = 1/2`,
`R = 1.5`, `t = y = 1`), and in case (a) `β̄ < 1 ∨ F̄(R) > 0` (otherwise, with every consumer a
reward consumer and `R` beyond the top of `F`'s support, every price above that top can be optimal:
`F = U[0,100]`, `G = U[0,10]`, `q = 10`, `β̄ = 1`, `λ = 1/2`, `R = 250`, `t = y = 1`, where
`p^c = 50` and `p* = 300` is optimal). In case (b) `F̄(R) ≥ F̄(p^c) > 0` holds automatically. `p*` and `p^c` are quantified maximizers, not closed forms; the
conclusion is stated for every maximizer. -/
theorem proposition_1 (P : Params) (h1 : P.A1) (h2 : P.A2) (h3 : P.A3) (hreg : P.Regular)
    (hβ : 0 < P.βbar) (t y : ℕ) (ht : 1 ≤ t) (hy : 1 ≤ y)
    (hΔ : 0 < P.Fbar (P.Δ (t - 1) y)) :
    ((∃ p : ℝ, 0 ≤ p ∧ IsMaxOn (fun x => P.J t x y) (Set.Ici 0) p) ∧
        ∃ pc : ℝ, IsMaxOn (fun x => P.Jc t x y) Set.univ pc) ∧
      ∀ pstar pc : ℝ, 0 ≤ pstar → IsMaxOn (fun x => P.J t x y) (Set.Ici 0) pstar →
        IsMaxOn (fun x => P.Jc t x y) Set.univ pc → 0 < P.g (pc / P.q) →
          (pc < P.R → (P.βbar < 1 ∨ 0 < P.Fbar P.R) → pc < pstar ∧ pstar < P.R) ∧
            (P.R < pc → P.R < pstar ∧ pstar < pc) := by sorry

end PointRedemption
