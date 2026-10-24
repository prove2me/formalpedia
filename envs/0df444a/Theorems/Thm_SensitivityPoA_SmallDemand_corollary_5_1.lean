-- Prove2me | Theorems.Thm_SensitivityPoA_SmallDemand_corollary_5_1
-- name    : SensitivityPoA.SmallDemand.corollary_5_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T17:39:22.071652+00:00
-- url     : https://prove2.me/theorems/1e30c237-0c9d-44b0-b5d6-c932959b70d7
-- title:
--   Corollary 5.1, p. 43 — for small total demand, ρ(τ, d) ≤ 1 + 8·|A|·(|K|+1)/τmin(0) · M_τ · T(d)
-- statement:
--   Fix a structure satisfying the standing assumptions, with $|A|$ arcs and $|\mathcal K|$ O/D pairs. Let $\tau = (\tau_a)_{a \in A}$ be cost functions defined on $[0, \infty)$ (continuous, non-decreasing and non-negative there), strictly positive on $[0,\infty)$, and Lipschitz continuous on a compact interval $[0, b]$, $b \in (0,\infty)$, with Lipschitz constant $M_\tau > 0$. Let
--   $$\tau_{\min}(0) = \min_{a \in A} \tau_a(0) > 0.$$
--   Then there is $\delta > 0$ such that every game $\Gamma = (\tau, d)$ with demand $d \ge 0$ and total demand $0 < T(d) < \delta$ satisfies
--   $$\rho(\Gamma) \le 1 + \frac{8 \cdot |A| \cdot (|\mathcal K| + 1)}{\tau_{\min}(0)} \cdot M_\tau \cdot T(d).$$
--
--   In particular, on the cost slice of $\tau$ the price of anarchy tends to $1$, at least linearly in the total demand, as the total demand tends to $0$.
--
--   **Formalization Note** The corollary as printed reads $\rho(\Gamma) \le 1 + \frac{8 \cdot M_\tau \cdot |A| \cdot (|\mathcal K|+1)}{\tau_{\min}(0)} \cdot M_\tau \cdot T(d)$, with $M_\tau$ twice. The display it summarizes (p. 43, second display) and the dimensions of the bound have $M_\tau$ once, which is what is posed; it implies the printed form whenever $M_\tau \ge 1$, the convention adopted on p. 30. "Strictly positive" is read as $\tau_a(x) > 0$ for all $x \ge 0$, which gives $\tau_{\min}(0) > 0$. "When the total demand $T(d)$ is small" is read as the existence of one threshold $\delta > 0$, chosen before $d$ and depending only on $\tau$. The games of the cost slice $\mathcal G(G,\mathcal K,\mathcal S)_{|\tau}$ coincide with $(\tau, d)$ on $[0, T(d)]$, and $\rho$ depends only on these values, so the statement is posed for $(\tau, d)$ itself. Under these hypotheses $(\tau, d)$ lies in the game space.
-- source:
--   Wu, Möhring, A sensitivity analysis of the PoA in non-atomic congestion games, arXiv:2007.13979v3 (2021), p. 43, Corollary 5.1

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_SensitivityPoA_SmallDemand_Setting

namespace SensitivityPoA.SmallDemand

open KellyStochasticNetworks

/-- Corollary 5.1, p. 43: for costs `τ_a` strictly positive on `[0, ∞)` and Lipschitz on `[0, b]`
with constant `M_τ > 0`, there is `δ > 0` such that every game `Γ = (τ, d)` with
`0 < T(d) < δ` has `ρ(Γ) ≤ 1 + 8·|A|·(|K|+1)/τmin(0) · M_τ · T(d)`, `τmin(0) = min_a τ_a(0)`. -/
theorem corollary_5_1 (N : Network) (hN : N.Standing) (τ : Fin N.J → ℝ → ℝ)
    (hτ : ∀ j, IsCostFn (τ j)) (hpos : ∀ j, ∀ x, 0 ≤ x → 0 < τ j x)
    (b : ℝ) (hb : 0 < b) (Mτ : ℝ) (hM : 0 < Mτ) (hLip : ∀ j, LipOnIcc (τ j) b Mτ)
    (τmin : ℝ) (hτmin : IsLeast (Set.range fun j => τ j 0) τmin) :
    ∃ δ > 0, ∀ d : Fin N.Sd → ℝ, (∀ k, 0 ≤ d k) → 0 < totalDemand d → totalDemand d < δ →
      PoA (⟨τ, d⟩ : Game N) ≤
        1 + 8 * (N.J : ℝ) * ((N.Sd : ℝ) + 1) / τmin * Mτ * totalDemand d := by sorry

end SensitivityPoA.SmallDemand
