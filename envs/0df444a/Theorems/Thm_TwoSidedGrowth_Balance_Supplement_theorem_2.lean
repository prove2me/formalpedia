-- Prove2me | Theorems.Thm_TwoSidedGrowth_Balance_Supplement_theorem_2
-- name    : TwoSidedGrowth.Balance.Supplement.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T03:32:37.863907+00:00
-- url     : https://prove2.me/theorems/25d6a812-7134-4a94-a51f-ebeebe39980a
-- title:
--   Theorem 2 (corrected: discounted saddle) — unique stationary state and Cobb–Douglas formulas
-- statement:
--   Let the model satisfy the published standing assumptions, with $\alpha\ne1$. A stationary state is defined by the maximum-principle system $\dot x=0$, $H_\pi=0$, maximization in $\gamma\in[0,1]$, and $\rho\psi-H_x=0$, for the current-value Hamiltonian specified above. There is exactly one such state $(x^*,\gamma^*,\pi^*,\psi^*)$. Its output is positive, $\psi^*=1$, and
--   $$
--   x^*=\left\{\frac{b(\gamma^*)+\rho}{(v-c)\alpha h(\gamma^*)}\right\}^{1/(\alpha-1)},\qquad
--   \gamma^*=\gamma^*(x^*),\qquad
--   \pi^*=v-c-\frac{b(\gamma^*)x^*}{g(\gamma^*,x^*)}.
--   $$
--   Here $\gamma^*(x)$ is exactly the clamped inverse (14), represented by the published `IsBalance` predicate, not an assumed optimizer.
--
--   For every Cobb–Douglas specialization with positive $A,a_s,a_d$ and $\alpha=a_s+a_d$, the stationary size and balance equal the full closed forms $x_{\rm CD}$ and $\gamma_{\rm CD}$ displayed in the definition item. This specialization does not restrict the general stationary theorem.
--
--   When $\alpha<1$, $x^*$ uniquely maximizes $W(x)=G(\gamma^*(x),x)$ over all $x>0$, giving the saturation size. When $\alpha>1$, $x^*$ uniquely minimizes $W$ in size and also uniquely minimizes $G(\gamma^*,x)$ over size at the fixed stationary balance, while $\gamma^*$ uniquely maximizes $G(\cdot,x^*)$ in balance. This is the discounted saddle interpretation, not a global maximum of the dynamic objective (13).
--
--   This result supplies the same stationary threshold to both growth-comparison theorems.
--
--   **Formalization Note** Existence and uniqueness are conclusions. Boundary balances are included, with positivity of stationary output deduced rather than assumed. All real powers and divisions occur on the source’s positive-size, nonconstant-returns domain.
--
--   Differences from the source:
--   - encoding: the section’s standing production and regularity assumptions → the unchanged published Model.Standing, including α>0, c<v and continuity of h on [0,1]; reason: these three disclosed base conventions are inherited; no new regularity is imposed or base item changed
--   - encoding: the stationary formula has exponent 1/(α−1) → α≠1 is explicit; reason: the displayed formula is undefined at α=1, whose separate perfect-matching regime is outside these companions
--   - correction: the p. 51 proof writes (1−ψ)πh(γ)x^α after Hπ=0, and a strict H comparison even for the same balance → actual Hπ=(1−ψ)out and weak maximization over all balances; reason: differentiate the printed Hamiltonian; strict comparison with oneself is impossible, while (47) and (48) use ordinary maximization
--   - correction: p. 53 says H(x,π,γ∗(x),1) has its size minimum at x∗ → W=H−ρx has the size minimum, with balance maximized; reason: (48) gives Hx=ρ>0 at x∗; for g=sd, α=2, βs0=βd0=ρ=1 and v−c=4, H=x²−x whereas W=x²−2x and x∗=1; see DISPROOF.md
--   - encoding: the stationary size and balance are named implicitly by their equations → choose from the maximum-principle equations and prove unique existence, ψ=1, positive output, and the steady margin; reason: these are consequences of the source system, not premises or definitions by the target formulas
-- source:
--   Lian, van Ryzin, Optimal Growth in Two-Sided Markets, SSRN working paper 3310559 (version of 2020-01-16), pp. 20–21, Theorem 2; pp. 51–53, proof and (47)–(48)

import Mathlib
import Definitions.Def_TwoSidedGrowth_Balance_Supplement_Stationary

namespace TwoSidedGrowth.Balance.Supplement

/-- Theorem 2, with its §4.2 Cobb–Douglas formulas and saturation/saddle context.
The printed H-minimum assertion is corrected to G = H - ρx, as (48) requires.
Existence is a conclusion; no stationary size, output positivity at an endpoint,
or curvature of optimized welfare is supplied as a hypothesis. -/
theorem theorem_2 (M : Model) (hM : M.Standing) (hα : M.α ≠ 1) :
    (∃! z : StationaryState, IsStationary M z) ∧
    IsStationary M (stationaryState M) ∧
    (stationaryState M).ψ = 1 ∧
    0 < h M (stationaryState M).γ ∧
    IsBalance M (stationarySize M) (stationaryState M).γ ∧
    (stationaryState M).γ = balance M (stationarySize M) ∧
    stationarySize M =
      ((attrition M (stationaryState M).γ + M.ρ) /
        ((M.v - M.c) * M.α * h M (stationaryState M).γ)) ^ (1 / (M.α - 1)) ∧
    (stationaryState M).pm = M.v - M.c -
      attrition M (stationaryState M).γ * stationarySize M /
        out M (stationaryState M).γ (stationarySize M) ∧
    (∀ A as ad : ℝ, IsCobbDouglas M A as ad →
      stationarySize M = cobbSize M A as ad ∧
      (stationaryState M).γ = cobbBalance M as ad) ∧
    (M.α < 1 → ∀ x : ℝ, 0 < x → x ≠ stationarySize M →
      W M x < W M (stationarySize M)) ∧
    (1 < M.α →
      (∀ x : ℝ, 0 < x → x ≠ stationarySize M →
        W M (stationarySize M) < W M x) ∧
      (∀ x : ℝ, 0 < x → x ≠ stationarySize M →
        G M (stationaryState M).γ (stationarySize M) < G M (stationaryState M).γ x) ∧
      (∀ η ∈ Set.Icc (0 : ℝ) 1, η ≠ (stationaryState M).γ →
        G M η (stationarySize M) < G M (stationaryState M).γ (stationarySize M))) := by sorry

end TwoSidedGrowth.Balance.Supplement
