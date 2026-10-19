-- Prove2me | Theorems.Thm_PoSShares_Stability_proposition_4
-- name    : PoSShares.Stability.proposition_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:30:39.139981+00:00
-- url     : https://prove2.me/theorems/84d9cbf1-0509-4ba4-bdbd-402a1ecaae13
-- title:
--   Proposition 4 — under $R_t = \rho N_{t-1}^\gamma$, $\lim_{N\to\infty}\mathbb{P}(|\pi_{1,\infty}-\pi_1|\ge\varepsilon)=0$ for all $\varepsilon>0$ iff $\gamma<1$
-- statement:
--   Suppose there are no coin transactions among the investors, and the coin reward grows with the number of coins outstanding as
--   $$R_t = \rho\,N_{t-1}^{\gamma}, \qquad \rho, \gamma > 0.$$
--   Fix investor 1's initial share $\pi_1 \in (0, 1)$. For each initial number of coins $N \in \mathbb{N}$ consider the PoS model with $N_0 = N$ and endowment $n_0 = \pi_1 N$, all on one probability space, and let $\pi_{1,\infty}$ (depending on $N$) be a measurable almost-sure limit of investor 1's share (Proposition 1). Then
--   $$\lim_{N \to \infty} \mathbb{P}\big(|\pi_{1,\infty} - \pi_1| \ge \varepsilon\big) = 0 \ \text{ for every } \varepsilon > 0 \quad \Longleftrightarrow \quad \gamma < 1.$$
--
--   Investor shares are therefore stable in the strict sense, concentrating at the initial share as the economy grows, exactly when the reward grows slower than linearly in the coin supply.
--
--   **Formalization Note.** The hypothesis $0 < \pi_1 < 1$ is added: for $\pi_1 \in \{0, 1\}$ the share never moves and the "only if" fails. The endowment $\pi_1 N$ is real (the paper's endowments are integers). The selection rule is $\mathbb{E}[\mathbf{1}_{S_{t+1}} \mid \mathcal{F}_t] = \pi_t$, investor 1 is tracked and the other investors enter only through $N_t$. The model with index $N = 0$ is unconstrained beyond the shared hypotheses.
-- source:
--   Roşu, Saleh, Evolution of Shares in a Proof-of-Stake Cryptocurrency, author's manuscript of July 30, 2020 (sha256 90d9c06b…2b35eb), p. 14, Proposition 4 (proof pp. 23–24)

import Mathlib
import Definitions.Def_PoSShares_Stability_Model

open MeasureTheory ProbabilityTheory Filter Topology

namespace PoSShares.Stability

/-- **Proposition 4**, p. 14 (proof pp. 23–24). Roşu, Saleh, *Evolution of Shares in a Proof-of-Stake Cryptocurrency*, author's manuscript of
July 30, 2020 (sha256 90d9c06b…2b35eb).

Suppose there are no coin transactions among the investors, and the coin reward is
`R_t = ρ N_{t−1}^γ` with constants `ρ, γ > 0`. Consider the family of models indexed by the
initial number of coins `N = N_0`, with investor 1's initial share fixed at `π_1` (endowment
`n_1 = π_1 N`), and let `π_{1,∞}` be the almost-sure limit of her share (Proposition 1). Then
`lim_{N→∞} P(|π_{1,∞} − π_1| ≥ ε) = 0` for every `ε > 0` if and only if `γ < 1`.

**Formalization Note.**
* `0 < π_1 < 1` is added: for `π_1 ∈ {0, 1}` the share never moves and the "only if" fails; the
  proof divides by `π_1(1 − π_1)` (p. 24).
* All models of the family live on one probability space (a family on separate spaces can be moved
  to a product space without changing any law). The model with index `N ≥ 1` has `N_0 = N`; the
  index-0 model is constrained only by the structure and the shared hypotheses.
* The endowment `π_1 N` is real (the paper has integer endowments).
* The selection rule is the conditional-expectation condition `IsPoS`; investor 1 is tracked and
  the other investors enter only through `N_t` (§3.3.1).
* `π_{1,∞}` is any measurable almost-sure limit of the shares; Proposition 1 provides one. -/
theorem proposition_4 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ρ γ π₁ : ℝ) (hρ : 0 < ρ) (hγ : 0 < γ) (hπ₁ : π₁ ∈ Set.Ioo (0 : ℝ) 1)
    (M : ℕ → Model Ω) (hPoS : ∀ N, IsPoS μ (M N))
    (hN : ∀ N : ℕ, 1 ≤ N → (M N).N₀ = N) (hn : ∀ N, (M N).n₀ = π₁ * (M N).N₀)
    (hR : ∀ N, IsPowerReward ρ γ (M N).N₀ (M N).R)
    (πinf : ℕ → Ω → ℝ) (hmeas : ∀ N, Measurable (πinf N))
    (hlim : ∀ N, ∀ᵐ ω ∂μ, Tendsto (fun t => share (M N) t ω) atTop (𝓝 (πinf N ω))) :
    (∀ ε : ℝ, 0 < ε →
        Tendsto (fun N => μ.real {ω | ε ≤ |πinf N ω - π₁|}) atTop (𝓝 0)) ↔ γ < 1 := by sorry

end PoSShares.Stability
