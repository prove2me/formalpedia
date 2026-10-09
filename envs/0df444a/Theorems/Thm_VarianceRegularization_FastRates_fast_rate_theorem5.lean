-- Prove2me | Theorems.Thm_VarianceRegularization_FastRates_fast_rate_theorem5
-- name    : VarianceRegularization.FastRates.fast_rate_theorem5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T20:04:38.39142+00:00
-- url     : https://prove2.me/theorems/f19817f8-d6ae-402d-bdd7-1389f63bd289
-- title:
--   Theorem 5 — fast rates for approximate robust minimizers under a growth condition
-- statement:
--   Let $\Theta\subseteq\mathbb R^d$ be convex and let the loss $\ell(\cdot;x)$ be convex and $L$-Lipschitz on $\Theta$ for every $x\in\mathcal X$ ($L\ge0$), with $\ell(\theta;\cdot)$ measurable and $P$-integrable for every $\theta\in\Theta$. Let $R(\theta)=\mathbb E_P[\ell(\theta;X)]$, let its solution set $S_\star$ be nonempty and closed, and for constants $\lambda>0$, $\gamma>1$, $r>0$ assume the growth condition
--   $$R(\theta)-\inf_{\theta\in\Theta}R(\theta)\ \ge\ \lambda\,\mathrm{dist}(\theta,S_\star)^\gamma\quad\text{for all }\theta\in\Theta\text{ with }\mathrm{dist}(\theta,S_\star)\le r.\tag{26}$$
--   Let $X_1,\dots,X_n$ be i.i.d. from $P$, $n\ge1$, $\rho\ge0$, $t>0$. If $0<\epsilon\le\frac12\lambda r^\gamma$ satisfies
--   $$\epsilon\ \ge\ \Big(2\frac{8^\gamma L^\gamma}{\lambda}\Big)^{\frac1{\gamma-1}}\Big(\frac\rho n\Big)^{\frac{\gamma}{2(\gamma-1)}}\quad\text{and}\quad\frac\epsilon2\ \ge\ 2\mathbb E[\mathfrak R_n(S_\star^{2\epsilon})]+L\Big(\frac{2\epsilon}{\lambda}\Big)^{\frac1\gamma}\sqrt{\frac{2t}{n}},\tag{27}$$
--   then
--   $$\mathbb P\big(\widehat S_\star^\epsilon\subset S_\star^{2\epsilon}\big)\ \ge\ 1-e^{-t}.$$
--   Here $S_\star^{\epsilon}$ and $\widehat S_\star^\epsilon$ are the $\epsilon$-suboptimal sets of the risk and of the robust risk $R_n(\cdot,\mathcal P_n)$, and $\mathfrak R_n(A)$ is the empirical Rademacher complexity of the localized class $\{\ell(\theta;\cdot)-\ell(\pi_{S_\star}(\theta);\cdot):\theta\in A\}$.
--
--   The theorem shows that approximate minimizers of the $\chi^2$-robust risk enjoy the same fast rates as empirical risk minimization when the risk has curvature: the accuracy $\epsilon$ can be as small as the localized Rademacher complexity and $(\rho/n)^{\gamma/(2(\gamma-1))}$, e.g. of order $1/n$ for quadratic growth ($\gamma=2$).
--
--   **Formalization Note** The paper prints $0\le\epsilon$; the statement is false at $\epsilon=0$ (with $\rho=0$ both conditions of (27) hold, yet for $\ell(\theta;x)=\frac12(\theta-x)^2$ on $\Theta=[-1,1]$, $X$ uniform on $[-\frac12,\frac12]$, the robust minimizer is the sample mean, almost surely $\ne0$), and its proof on p. 45 divides by $\epsilon$; the theorem is stated for $0<\epsilon$. $S_\star$ nonempty and closed are the presuppositions of the projection $\pi_{S_\star}$. The expected Rademacher complexity is assumed integrable over the sample. The event is stated as $P^{\otimes n}(\widehat S_\star^\epsilon\not\subset S_\star^{2\epsilon})\le e^{-t}$, with the outer measure if the event is not measurable.
-- source:
--   Duchi and Namkoong, Variance-based regularization with convex objectives, arXiv:1610.02581v3 (2017), p. 19, Theorem 5, eqs. (26)-(27); proof in Appendix E, pp. 44-46

import Mathlib
import Definitions.Def_VarianceRegularization_FastRates_RobustRisk
import Definitions.Def_VarianceRegularization_FastRates_Setting
open MeasureTheory

namespace VarianceRegularization.FastRates

/-- Duchi–Namkoong, arXiv:1610.02581v3, p. 19, Theorem 5 (corrected: `0 < ε` instead of the
printed `0 ≤ ε`). Let `Θ ⊆ ℝᵈ` be convex and `ℓ(·; x)` convex and `L`-Lipschitz on `Θ` for
every `x`. Let `λ > 0`, `γ > 1`, `r > 0` and assume the growth condition (26)
`R(θ) − inf_Θ R ≥ λ dist(θ, S_⋆)^γ` whenever `dist(θ, S_⋆) ≤ r`. Let `t > 0`. If
`0 < ε ≤ ½ λ r^γ` satisfies (27),
`ε ≥ (2·8^γ L^γ/λ)^{1/(γ−1)} (ρ/n)^{γ/(2(γ−1))}` and
`ε/2 ≥ 2 𝔼[𝔑_n(S_⋆^{2ε})] + L (2ε/λ)^{1/γ} √(2t/n)`, then `ℙ(Ŝ_⋆^ε ⊂ S_⋆^{2ε}) ≥ 1 − e^{−t}`,
stated as `P^{⊗n}(Ŝ_⋆^ε ⊄ S_⋆^{2ε}) ≤ e^{−t}`.

At `ε = 0` the printed statement is false: with `ρ = 0` both conditions of (27) hold and the
conclusion says empirical minimizers lie in `S_⋆` with probability `≥ 1 − e^{−t}`; for
`ℓ(θ; x) = ½(θ − x)²` on `Θ = [−1, 1]`, `X ∼ Unif[−½, ½]` (`L = 3/2`, `γ = 2`, `λ = ½`,
`r = 1`) the minimizer is the sample mean, almost surely `≠ 0`. The proof (p. 45) divides by
`ε`. `S_⋆` nonempty and closed are the presuppositions of the projection `π_{S_⋆}`; the
expected Rademacher complexity is assumed integrable over the sample. -/
theorem fast_rate_theorem5
{X : Type*} [MeasurableSpace X] (P : Measure X) [IsProbabilityMeasure P] {d : ℕ}
    (Θ : Set (EuclideanSpace ℝ (Fin d))) (hΘ : Convex ℝ Θ)
    (ℓ : EuclideanSpace ℝ (Fin d) → X → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hconv : ∀ x, ConvexOn ℝ Θ (fun θ => ℓ θ x))
    (hlip : ∀ x, ∀ θ ∈ Θ, ∀ θ' ∈ Θ, |ℓ θ x - ℓ θ' x| ≤ L * ‖θ - θ'‖)
    (hmeas : ∀ θ ∈ Θ, Measurable (ℓ θ)) (hint : ∀ θ ∈ Θ, Integrable (ℓ θ) P)
    (hS_ne : (subOptSet Θ ℓ P 0).Nonempty) (hS_closed : IsClosed (subOptSet Θ ℓ P 0))
    (lam γ r : ℝ) (hlam : 0 < lam) (hγ : 1 < γ) (hr : 0 < r)
    (hgrowth : ∀ θ ∈ Θ, Metric.infDist θ (subOptSet Θ ℓ P 0) ≤ r →
      ∀ θs ∈ subOptSet Θ ℓ P 0,
        lam * Metric.infDist θ (subOptSet Θ ℓ P 0) ^ γ ≤ risk ℓ P θ - risk ℓ P θs)
    (n : ℕ) (hn : 0 < n) (ρ : ℝ) (hρ : 0 ≤ ρ) (t : ℝ) (ht : 0 < t)
    (ε : ℝ) (hε : 0 < ε) (hεr : ε ≤ (1 / 2) * lam * r ^ γ)
    (hRint : Integrable (fun s : Fin n → X => localizedRademacher Θ ℓ P (subOptSet Θ ℓ P (2 * ε)) s)
      (Measure.pi (fun _ : Fin n => P)))
    (h27a : (2 * (8 ^ γ * L ^ γ) / lam) ^ (1 / (γ - 1)) * (ρ / n) ^ (γ / (2 * (γ - 1))) ≤ ε)
    (h27b : 2 * (∫ s, localizedRademacher Θ ℓ P (subOptSet Θ ℓ P (2 * ε)) s
                ∂(Measure.pi (fun _ : Fin n => P)))
              + L * (2 * ε / lam) ^ (1 / γ) * Real.sqrt (2 * t / n) ≤ ε / 2) :
    Measure.pi (fun _ : Fin n => P) {s | ¬ empSubOptSet Θ ρ ℓ s ε ⊆ subOptSet Θ ℓ P (2 * ε)}
      ≤ ENNReal.ofReal (Real.exp (-t)) := by sorry

end VarianceRegularization.FastRates
