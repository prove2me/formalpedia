-- Prove2me | Theorems.Thm_RoboAdvising_Interaction_proposition_5_1_ii
-- name    : RoboAdvising.Interaction.proposition_5_1_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:17:50.27022+00:00
-- url     : https://prove2.me/theorems/3fcec58c-5bef-467f-8f2a-53a936530cea
-- title:
--   Proposition 5.1(ii) and (5.6), pp. 21–22 — argmin_{φ≥1} R̃ is 1 (β = 0), a unique φ0 (β, pϵ > 0) or ∞ (pϵ = 0); φ0 ↑ in β, σ0 and ↓ in pϵ, σϵ
-- statement:
--   Let $\sigma_0 > 0$, $\sigma_\epsilon > 0$, $p_\epsilon \in [0,1]$ and $\beta \ge 0$ with $\beta + p_\epsilon > 0$, and let
--   $$\widetilde{\mathcal R}(\phi,\beta) = \sqrt{\frac{2}{\pi}}\left(\frac{\beta\sigma_0}{\sqrt{\phi}}\Big(1-\frac{\phi-1}{2}p_\epsilon\Big) + \sqrt{\frac{\beta^2\sigma_0^2}{\phi}+\sigma_\epsilon^2}\;\frac{\phi-1}{2}p_\epsilon\right)$$
--   be the approximate personalization measure. Call $\phi$ a minimizer if $\phi\ge1$ and $\widetilde{\mathcal R}(\phi,\beta)\le\widetilde{\mathcal R}(\psi,\beta)$ for all $\psi\ge1$. Then
--   $$\arg\min_{\phi\ge1}\widetilde{\mathcal R}(\phi,\beta) = \begin{cases} 1, & \beta = 0,\\ \phi_0\in[1,\infty), & \beta>0,\ p_\epsilon>0,\\ \infty, & p_\epsilon = 0,\end{cases}$$
--   in the following precise sense:
--
--   1. if $\beta = 0$, then $\phi = 1$ is the unique minimizer;
--   2. if $\beta > 0$ and $p_\epsilon > 0$, there is exactly one minimizer $\phi_0$;
--   3. if $p_\epsilon = 0$, there is no minimizer: $\widetilde{\mathcal R}$ is strictly decreasing on $[1,\infty)$ and tends to $0$ as $\phi\to\infty$.
--
--   Furthermore, for $\beta>0$ and $p_\epsilon>0$ the minimizer $\phi_0$ satisfies the monotonicity properties (5.6): it is increasing in $\beta$ and in $\sigma_0$, and decreasing in $p_\epsilon$ and in $\sigma_\epsilon$. Precisely, if one of these parameters is raised (keeping $p_\epsilon \le 1$) and $\phi_0'$ is the minimizer for the new parameters, then $\phi_0 \le \phi_0'$ for $\beta$ and $\sigma_0$ and $\phi_0' \le \phi_0$ for $p_\epsilon$ and $\sigma_\epsilon$, with strict inequality whenever $\phi_0 > 1$.
--
--   The proposition says that without behavioral bias the robo-advisor should interact with the client at every period, that without idiosyncratic shocks it should never interact, and that in between there is a unique optimal time between interactions, which grows with the bias and with market volatility.
--
--   **Formalization Note** The page writes (5.6) as strict signs of the partial derivatives $\partial\phi_0/\partial\beta > 0$, $\partial\phi_0/\partial\sigma_0 > 0$, $\partial\phi_0/\partial p_\epsilon < 0$, $\partial\phi_0/\partial\sigma_\epsilon < 0$. These are false as printed on the open parameter region where the minimizer is the corner $\phi_0 = 1$ (for example $\beta = \sigma_0 = 1$, $\sigma_\epsilon = 3$, $p_\epsilon = 1$), where $\phi_0$ is locally constant, and $\phi_0$ is not differentiable across the boundary of that region. The statement therefore formalizes (5.6) as monotone comparative statics: weak monotonicity everywhere, strict whenever the starting minimizer exceeds $1$. The case "$\arg\min = \infty$" is read as: no $\phi\ge1$ attains the infimum, $\widetilde{\mathcal R}$ strictly decreases on $[1,\infty)$ and converges to its infimum $0$. $\phi$ is real (the model of §5.1 uses integer $\phi$; the proposition differentiates in $\phi$). The monotonicity clauses quantify over minimizers of two parameter sets; clause 2 guarantees both exist, so they are not vacuous.
-- source:
--   Capponi, Ólafsson, Zariphopoulou, Personalized Robo-Advising: Enhancing Investment through Client Interaction, arXiv:1911.01391v2, pp. 21–22, Proposition 5.1(ii) and (5.6)

import Mathlib
import Definitions.Def_RoboAdvising_Interaction_Model

namespace RoboAdvising.Interaction


/-- Proposition 5.1(ii) and (5.6), pp. 21–22. Under the standing ranges and `β + pϵ > 0`:
the minimizer of `R̃` over `φ ≥ 1` is `1` when `β = 0`; it exists and is unique when `β > 0`,
`pϵ > 0`; when `pϵ = 0` there is none (`R̃` strictly decreases to its infimum `0`, i.e. the
minimizer is "∞"). The minimizer `φ0` is weakly increasing in `β` and `σ0` and weakly decreasing
in `pϵ` and `σϵ`, strictly whenever the starting minimizer exceeds `1`. -/
theorem proposition_5_1_ii (P : Params) (hS : P.Standing) (hpos : 0 < P.β + P.pe) :
    (P.β = 0 → ∀ φ : ℝ, IsOptInteraction P φ ↔ φ = 1) ∧
    (0 < P.β → 0 < P.pe → ∃! φ0 : ℝ, IsOptInteraction P φ0) ∧
    (P.pe = 0 → (∀ φ : ℝ, ¬ IsOptInteraction P φ) ∧ StrictAntiOn (Rtilde P) (Set.Ici 1) ∧
        Filter.Tendsto (Rtilde P) Filter.atTop (nhds 0)) ∧
    (0 < P.β → 0 < P.pe → ∀ β' φ φ' : ℝ, P.β < β' →
        IsOptInteraction P φ → IsOptInteraction { P with β := β' } φ' →
        φ ≤ φ' ∧ (1 < φ → φ < φ')) ∧
    (0 < P.β → 0 < P.pe → ∀ s' φ φ' : ℝ, P.sig0 < s' →
        IsOptInteraction P φ → IsOptInteraction { P with sig0 := s' } φ' →
        φ ≤ φ' ∧ (1 < φ → φ < φ')) ∧
    (0 < P.β → 0 < P.pe → ∀ p' φ φ' : ℝ, P.pe < p' → p' ≤ 1 →
        IsOptInteraction P φ → IsOptInteraction { P with pe := p' } φ' →
        φ' ≤ φ ∧ (1 < φ → φ' < φ)) ∧
    (0 < P.β → 0 < P.pe → ∀ s' φ φ' : ℝ, P.se < s' →
        IsOptInteraction P φ → IsOptInteraction { P with se := s' } φ' →
        φ' ≤ φ ∧ (1 < φ → φ' < φ)) := by sorry
end RoboAdvising.Interaction
