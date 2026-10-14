-- Prove2me | Theorems.Thm_SCInfoDesign_ValueInfo_theorem_2
-- name    : SCInfoDesign.ValueInfo.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T23:29:30.521117+00:00
-- url     : https://prove2.me/theorems/a2ef2d9d-e40a-4119-9a6f-46d56d64e000
-- title:
--   Theorem 2, p. 13 — for ξ ∈ (0, τ̲(p₀)], VI_ND is unimodal in p₀ (peak √(ξ(b₀ − a₀)/(a₁ − a₀))) and decreasing in ξ; VI_FD is decreasing in p₀ and unimodal in ξ (peak ξ*)
-- statement:
--   Let the demand supports be nested, $0\le a_0<a_1<b_1\le b_0$, and consider the partial-disclosure regime $\xi\in(0,\underline\tau(p_0)]$, where $\underline\tau(p_0)=p_0(a_1-a_0)/(b_0-a_0)$. Let $VI_{ND}(\xi,p_0)$ be the retailer's expected cost under no disclosure minus her optimal expected cost, and $VI_{FD}(\xi,p_0)$ the cost under full disclosure minus the optimal cost. For fixed $\xi$, the regime is the set of priors $p_0\in[\hat p,1]$ with $\hat p=\xi(b_0-a_0)/(a_1-a_0)$, nonempty exactly when $\xi\le\underline\tau(1)$. Put
--   $$p_0^*=\sqrt{\frac{\xi(b_0-a_0)}{a_1-a_0}},\qquad \xi^*=1-\frac12\cdot\frac{a_1-a_0}{b_0-b_1+a_1-a_0}.$$
--   Then:
--
--   1. for every $\xi\in(0,\underline\tau(1)]$, $VI_{ND}(\xi,\cdot)$ is strictly increasing on $[\hat p,p_0^*]$ and strictly decreasing on $[p_0^*,1]$ (unimodal in $p_0$ with peak $p_0^*$);
--   2. for every $p_0\in(0,1)$, $VI_{ND}(\cdot,p_0)$ is strictly decreasing on $(0,\underline\tau(p_0)]$;
--   3. for every $\xi\in(0,\underline\tau(1)]$, $VI_{FD}(\xi,\cdot)$ is strictly decreasing on $[\hat p,1]$;
--   4. for every $p_0\in(0,1)$, $VI_{FD}(\cdot,p_0)$ is strictly increasing on $(0,\underline\tau(p_0)]\cap(-\infty,\xi^*]$ and strictly decreasing on $(0,\underline\tau(p_0)]\cap[\xi^*,\infty)$ (unimodal in $\xi$ with peak $\xi^*$).
--
--   The theorem describes how much a retailer gains from optimal information design over the two naive policies: the gain over no disclosure peaks at an intermediate prior and shrinks as the critical ratio grows, while the gain over full disclosure shrinks with the prior and peaks at an intermediate critical ratio.
--
--   **Formalization Note** The optimal expected cost is the infimum over all finite disclosure policies and all best responses of the supplier (Setting), not the cost of the paper's policy $\Gamma^*$. "Unimodal with peak $x^*$" is formalized as strictly increasing up to $x^*$ and strictly decreasing from $x^*$ on the regime; when $\xi^*$ lies outside $(0,\underline\tau(p_0)]$ one of the two pieces of item 4 is empty or a single point. The paper defines the value of information as an absolute value; both differences are nonnegative, so the differences are used. The $\xi$-claims are stated for $p_0<1$: at $p_0=1$ both values are $0$ for every $\xi$, so they decrease only weakly. The hypothesis $a_0<a_1$ is added: with $a_0=a_1$ the regime is empty and $\hat p$, $p_0^*$ are $0/0$. The nonnegativity of $a_0,a_1$ and $a_0<b_0$, $a_1<b_1$ are the paper's implicit standing assumptions.
-- source:
--   Candogan, Gurkan, The Value of Information Design in Supply Chain Management, SSRN 4378997 (preprint), p. 13, Theorem 2 (proof pp. 29–30, App. B)

import Mathlib
import Definitions.Def_BiconvexProg_BranchBound_convexEnvelope
import Definitions.Def_SCInfoDesign_ValueInfo_Setting

namespace SCInfoDesign.ValueInfo

/-- Theorem 2 (p. 13): in the partial-disclosure regime `ξ ∈ (0, τ̲(p₀)]` with nested supports
and `a₀ < a₁`,
1. `VI_ND` is unimodal in `p₀` with peak `p₀* = √(ξ(b₀ − a₀)/(a₁ − a₀))` (strictly increasing
   on `[p̂, p₀*]`, strictly decreasing on `[p₀*, 1]`);
2. `VI_ND` is strictly decreasing in `ξ` on `(0, τ̲(p₀)]` for `p₀ ∈ (0, 1)`;
3. `VI_FD` is strictly decreasing in `p₀` on `[p̂, 1]`;
4. `VI_FD` is unimodal in `ξ` on `(0, τ̲(p₀)]` with peak
   `ξ* = 1 − 1/2 × (a₁ − a₀)/(b₀ − b₁ + a₁ − a₀)`, for `p₀ ∈ (0, 1)`. -/
theorem theorem_2
    (P : Params) (hab₀ : P.a₀ < P.b₀) (hab₁ : P.a₁ < P.b₁) (ha₀ : 0 ≤ P.a₀) (ha₁ : 0 ≤ P.a₁)
    (hnest_a : P.a₀ ≤ P.a₁) (hnest_b : P.b₁ ≤ P.b₀)
    (hlt : P.a₀ < P.a₁) :
    (∀ ξ : ℝ, 0 < ξ → ξ ≤ τlow P 1 →
        StrictMonoOn (fun p₀ => VI_ND P ξ p₀) (Set.Icc (pHat P ξ) (p₀star P ξ)) ∧
        StrictAntiOn (fun p₀ => VI_ND P ξ p₀) (Set.Icc (p₀star P ξ) 1)) ∧
    (∀ p₀ : ℝ, 0 < p₀ → p₀ < 1 →
        StrictAntiOn (fun ξ => VI_ND P ξ p₀) (Set.Ioc 0 (τlow P p₀))) ∧
    (∀ ξ : ℝ, 0 < ξ → ξ ≤ τlow P 1 →
        StrictAntiOn (fun p₀ => VI_FD P ξ p₀) (Set.Icc (pHat P ξ) 1)) ∧
    (∀ p₀ : ℝ, 0 < p₀ → p₀ < 1 →
        StrictMonoOn (fun ξ => VI_FD P ξ p₀) (Set.Ioc 0 (τlow P p₀) ∩ Set.Iic (ξstar P)) ∧
        StrictAntiOn (fun ξ => VI_FD P ξ p₀) (Set.Ioc 0 (τlow P p₀) ∩ Set.Ici (ξstar P))) := by sorry

end SCInfoDesign.ValueInfo
