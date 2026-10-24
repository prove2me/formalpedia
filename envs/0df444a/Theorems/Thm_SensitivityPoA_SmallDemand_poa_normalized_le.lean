-- Prove2me | Theorems.Thm_SensitivityPoA_SmallDemand_poa_normalized_le
-- name    : SensitivityPoA.SmallDemand.poa_normalized_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T17:39:14.418996+00:00
-- url     : https://prove2.me/theorems/057b4dad-9094-4192-b872-232f66e30c49
-- title:
--   p. 43, second display — for small T(d), ρ(Γ′) = 1 and |ρ(Λ_{T(d)}(Γ)) − ρ(Γ′)| ≤ 8·|A|·(|K|+1)/τmin(0) · M_τ · T(d), uniformly in d
-- statement:
--   Fix a structure satisfying the standing assumptions, with $|A|$ arcs and $|\mathcal K|$ O/D pairs. Let $\tau = (\tau_a)_{a \in A}$ be cost functions (continuous, non-decreasing and non-negative on $[0,\infty)$) that are strictly positive on $[0, \infty)$ and Lipschitz on $[0, b]$ with constant $M_\tau > 0$, for some $b > 0$. Let $\tau_{\min}(0) = \min_a \tau_a(0)$ and $\sigma_a(x) \equiv \tau_a(0)$.
--
--   Then there is $\delta > 0$, depending only on $\tau$ (and the structure), such that for every demand vector $d \ge 0$ with $0 < T(d) < \delta$, writing $\Gamma = (\tau, d)$ and $\Gamma' = (\sigma, d/T(d))$,
--   $$\rho(\Gamma') = 1 \quad\text{and}\quad |\rho(\Lambda_{T(d)}(\Gamma)) - \rho(\Gamma')| \le \frac{8 \cdot |A| \cdot (|\mathcal K| + 1)}{\tau_{\min}(0)} \cdot M_\tau \cdot T(d).$$
--
--   This is the paper's application of its local Lipschitz estimate (4.33) at the constant-cost game $\Gamma'$, with a threshold and a constant that do not depend on $d$.
--
--   **Formalization Note** The page writes "when $T(d)$ is small"; this is posed as the existence of one $\delta > 0$ chosen before $d$. The page derives $\rho(\Gamma') = 1$ from the constancy of $\sigma$ ("Clearly, $\rho(\Gamma') \equiv 1$") and uses it in the display's last equality; it is stated here as a conjunct.
-- source:
--   Wu, Möhring, A sensitivity analysis of the PoA in non-atomic congestion games, arXiv:2007.13979v3 (2021), p. 43, §5.2, second display (application of (4.33))

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_SensitivityPoA_SmallDemand_Setting

namespace SensitivityPoA.SmallDemand

open KellyStochasticNetworks

/-- p. 43, second display: for costs `τ_a` strictly positive on `[0, ∞)` and `M_τ`-Lipschitz on
`[0, b]`, there is `δ > 0` (depending on `τ` only) such that for every demand vector `d` with
`0 < T(d) < δ`, the constant-cost game `Γ' = (σ, d/T(d))`, `σ_a ≡ τ_a(0)`, has `ρ(Γ') = 1` and
`|ρ(Λ_{T(d)}(Γ)) − ρ(Γ')| ≤ 8·|A|·(|K|+1)/τmin(0) · M_τ · T(d)` for `Γ = (τ, d)`. -/
theorem poa_normalized_le (N : Network) (hN : N.Standing) (τ : Fin N.J → ℝ → ℝ)
    (hτ : ∀ j, IsCostFn (τ j)) (hpos : ∀ j, ∀ x, 0 ≤ x → 0 < τ j x)
    (b : ℝ) (hb : 0 < b) (Mτ : ℝ) (hM : 0 < Mτ) (hLip : ∀ j, LipOnIcc (τ j) b Mτ)
    (τmin : ℝ) (hτmin : IsLeast (Set.range fun j => τ j 0) τmin) :
    ∃ δ > 0, ∀ d : Fin N.Sd → ℝ, (∀ k, 0 ≤ d k) → 0 < totalDemand d → totalDemand d < δ →
      PoA (⟨fun j _ => τ j 0, fun k => d k / totalDemand d⟩ : Game N) = 1 ∧
      |PoA (demandNormalize (totalDemand d) (⟨τ, d⟩ : Game N)) -
          PoA (⟨fun j _ => τ j 0, fun k => d k / totalDemand d⟩ : Game N)| ≤
        8 * (N.J : ℝ) * ((N.Sd : ℝ) + 1) / τmin * Mτ * totalDemand d := by sorry

end SensitivityPoA.SmallDemand
