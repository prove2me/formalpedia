-- Prove2me | Theorems.Thm_RegretBandits_Stochastic_alpha_psi_ucb_pseudo_regret
-- name    : RegretBandits.Stochastic.alpha_psi_ucb_pseudo_regret
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T02:34:00.426376+00:00
-- url     : https://prove2.me/theorems/cb749a99-5faf-4c06-b8b6-9fcdbae4ff60
-- title:
--   Theorem 2.1 — pseudo-regret of $(\alpha,\psi)$-UCB
-- statement:
--   Consider a stochastic bandit with $K\ge2$ arms of means $\mu_1,\dots,\mu_K$, $\mu^*=\max_i\mu_i$, gaps $\Delta_i=\mu^*-\mu_i$, whose reward distributions satisfy the moment condition (2.2) with a convex function $\psi$. Let $\psi^*$ be its Legendre–Fenchel transform, and assume:
--
--   1. $\psi(\lambda)\ge\psi(0)$ for every $\lambda\le0$;
--   2. $\psi^*(\varepsilon)<\infty$ for every $\varepsilon\ge0$;
--   3. $\psi^*(\Delta_i/2)>0$ for every arm with $\Delta_i>0$.
--
--   Then $(\alpha,\psi)$-UCB with $\alpha>2$ satisfies, for every horizon $n$,
--   $$\overline R_n\le\sum_{i:\Delta_i>0}\Delta_i\left(\frac{\alpha\ln n}{\psi^*(\Delta_i/2)}+\frac{\alpha}{\alpha-2}\right).$$
--
--   This is the logarithmic, distribution-dependent pseudo-regret bound of upper confidence bound strategies. For $[0,1]$ rewards it gives (2.4). Theorem 2.2 shows that its order $\ln n/\Delta_i$ cannot be improved in general.
--
--   **Formalization Note.** *Corrected misprint:* the book prints the constant term as $\alpha/(\alpha-2)$, not $\Delta_i\,\alpha/(\alpha-2)$. Its proof bounds $\mathbb E\,T_i(n)\le\alpha\ln n/\psi^*(\Delta_i/2)+\alpha/(\alpha-2)$ and multiplies by $\Delta_i$. The printed form is false when gaps can exceed $1$ (Gaussian rewards, $\psi(\lambda)=\sigma^2\lambda^2/2$, large $\Delta_i$). The hypotheses 1–3 are conventions the book leaves implicit. (1) makes (2.3) true: (2.2) constrains $\psi$ only on $\lambda\ge0$, while $\psi^*$ takes the supremum over all of $\mathbb R$. (2) makes $(\psi^*)^{-1}$ a genuine inverse, $\psi^*((\psi^*)^{-1}(y))\ge y$. (3) makes the printed bound a finite real number. All three hold for every $\psi$ in the book ($\lambda^2/8$, $\sigma^2\lambda^2/2$, $|\lambda|^p/p$ with $p>1$). The algorithm plays every arm once before using the index (the index is undefined at $T_j=0$). The arms played are assumed measurable so that $\overline R_n$ is a genuine expectation. The reward stack representation is described in `RegretBandits.Stochastic.model`.
-- source:
--   Bubeck, Cesa-Bianchi, Regret Analysis of Stochastic and Nonstochastic Multi-armed Bandit Problems, arXiv:1204.5721v2, p. 11, Theorem 2.1

import Mathlib
import Definitions.Def_ImprovedLinBandits_UCBDelta_armModel
import Definitions.Def_RegretBandits_Stochastic_model
import Definitions.Def_RegretBandits_Stochastic_alphaPsiUCB

namespace RegretBandits.Stochastic

open MeasureTheory ImprovedLinBandits.UCBDelta

/-- Theorem 2.1 of Bubeck and Cesa-Bianchi (arXiv:1204.5721v2, p. 11), in the form its proof
establishes (the printed constant term `α/(α-2)` is multiplied by `Δ_i`): if the reward
distributions satisfy (2.2), then (α, ψ)-UCB with `α > 2` satisfies, for every `n`,
`R̄_n ≤ ∑_{i : Δ_i > 0} Δ_i (α ln n / ψ*(Δ_i/2) + α/(α - 2))`.
Added conventions: `ψ ≥ ψ 0` on `(-∞, 0]`, `ψ*` finite on `[0, ∞)`, `ψ*(Δ_i/2) > 0`. -/
theorem alpha_psi_ucb_pseudo_regret {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {K : ℕ} (hK : 2 ≤ K) (X : Fin K → ℕ → Ω → ℝ) (μ : Fin K → ℝ)
    (hX : IsStochasticBandit P X μ) (ψ : ℝ → ℝ) (hψ : SatisfiesMomentCondition P ψ X μ)
    (hψneg : ∀ l : ℝ, l ≤ 0 → ψ 0 ≤ ψ l)
    (hψfin : ∀ ε : ℝ, 0 ≤ ε → legendreFenchel ψ ε ≠ ⊤)
    (hψpos : ∀ i, 0 < gap μ i → (0 : EReal) < legendreFenchel ψ (gap μ i / 2))
    (α : ℝ) (hα : 2 < α) (I : ℕ → Ω → Fin K) (hI : ∀ t, Measurable (I t))
    (hrun : IsAlphaPsiUCBRun ψ α X I) (n : ℕ) :
    pseudoRegretBar P μ I n ≤
      ∑ i ∈ Finset.univ.filter (fun i => 0 < gap μ i),
        gap μ i * (α * Real.log (n : ℝ) / (legendreFenchel ψ (gap μ i / 2)).toReal
          + α / (α - 2)) := by sorry

end RegretBandits.Stochastic
