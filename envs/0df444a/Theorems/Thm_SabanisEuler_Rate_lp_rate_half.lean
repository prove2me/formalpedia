-- Prove2me | Theorems.Thm_SabanisEuler_Rate_lp_rate_half
-- name    : SabanisEuler.Rate.lp_rate_half
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T23:25:43.035729+00:00
-- url     : https://prove2.me/theorems/d7a08f5a-2052-48c5-a446-71d4d8675515
-- title:
--   Theorem 2 — Lp-convergence of the tamed Euler scheme with order 1/2
-- statement:
--   Let $X$ solve the SDE $dX(t)=b(t,X(t))\,dt+\sigma(t,X(t))\,dW(t)$ on $[0,T]$, and for every $n\ge1$ let $X_n$ solve the tamed Euler scheme
--   $$dX_n(t)=b_n(t,X_n(\kappa_n(t)))\,dt+\sigma_n(t,X_n(\kappa_n(t)))\,dW(t),\qquad b_n=\frac{b}{1+n^{-1/2}|x|^l},\quad \sigma_n=\frac{\sigma}{1+n^{-1/2}|x|^l},$$
--   with the same initial value $X(0)$ and the same Wiener martingale $W$, where $\kappa_n(t)=\lfloor nt\rfloor/n$. Suppose A-2, A-4, A-5 and A-6 (with exponent $l$) hold, and that $l\le\frac{p_0-2}{4}$, $0<p<p_1$, $p\le\frac{p_0}{2l+1}$ (the $\mathfrak p$-condition), and $p_1>2$. Then there is a constant $C$, independent of $n$, such that for every $n\ge1$
--   $$\sup_{0\le t\le T}\mathbb E\big[|X(t)-X_n(t)|^p\big]\le Cn^{-p/2}.$$
--
--   This is the optimal strong rate $1/2$ of the Euler method, obtained for an explicit scheme although the drift and the diffusion coefficient may grow superlinearly; for globally Lipschitz coefficients it reduces to the classical result.
--
--   **Formalization Note** The hypothesis $p_1>2$ is added to the printed statement. The printed proof applies Itô's formula to $|X-X_n|^p$ for $p\ge2$ and uses $(1+\varepsilon)(p-1)\le p_1-1$, so it covers $2\le p<p_1$; an exponent $p<2$ is reduced to $p'=2$, which satisfies the $\mathfrak p$-condition exactly when $p_1>2$. At $p_1=2$ the paper's argument proves nothing. Expectations and the supremum are computed in $[0,\infty]$; the bound is stated as $\le C n^{-p/2}$ with $C$ real, chosen after all data of the problem and before $n$.
-- source:
--   Sabanis, Euler approximations with varying coefficients, arXiv:1308.1796v4, p. 6, Theorem 2, eq. (2.13)

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_SabanisEuler_Shared_Setting
import Definitions.Def_SabanisEuler_Shared_Conditions
import Definitions.Def_SabanisEuler_Shared_Model2

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
open SabanisEuler.Shared

namespace SabanisEuler.Rate

open EthierKurtz

/-- Sabanis (2016), arXiv:1308.1796v4, p. 6, Theorem 2, eq. (2.13): under A-2, A-4–A-6 and the
𝔭-condition (the scheme (2.2) uses the tamed coefficients (2.11)–(2.12) with `α = 1/2`,
`l ≤ (p₀ - 2)/4`, `0 < p < p₁`, `p ≤ p₀/(2l + 1)`), the scheme converges to the solution of
(2.1) in `𝓛^p` with order 1/2: there is a constant `C` independent of `n` with
`sup_{0 ≤ t ≤ T} 𝔼[|X(t) - Xₙ(t)|^p] ≤ C n^{-p/2}` for every `n ≥ 1`.
**Added hypothesis:** `2 < p₁` (`hp₁2`). The printed proof applies Itô's formula to
`|X - Xₙ|^p` for `p ≥ 2` and needs `(1 + ε)(p - 1) ≤ p₁ - 1`; it covers `2 ≤ p < p₁`, and
`p < 2` through `p' = 2`, which the 𝔭-condition admits exactly when `p₁ > 2`. At `p₁ = 2`
the paper's argument proves nothing. -/
theorem lp_rate_half
    {d d₁ : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℝ≥0 mΩ) [ℱ.IsRightContinuous]
    (W : ℝ≥0 → Ω → SDEState d₁) (hW : IsWienerMartingale P ℱ W)
    (T : ℝ≥0) (hT : 0 < T)
    (p₀ p₁ : ℝ) (hp₀ : 2 ≤ p₀) (hp₁ : 2 ≤ p₁) (hp₁2 : 2 < p₁)
    (b : ℝ≥0 × SDEState d → SDEState d) (σ : ℝ≥0 × SDEState d → Diffusion d d₁)
    (hb : Measurable b) (hσ : Measurable σ)
    (ξ : Ω → SDEState d) (hξ : Measurable[ℱ 0] ξ)
    (l : ℝ)
    (hA2 : CondA2 T b) (hA4 : CondA4 T p₀ b σ) (hA5 : CondA5 P p₀ ξ)
    (hA6 : CondA6 T p₁ l b σ)
    (p : ℝ) (hp : PCondition p₀ p₁ l p)
    (X : ℝ≥0 → Ω → SDEState d) (hX : IsSolution P ℱ W T ξ b σ X)
    (Xₙ : ℕ → ℝ≥0 → Ω → SDEState d)
    (hXₙ : ∀ n : ℕ, 1 ≤ n →
      IsSchemeSolution P ℱ W T ξ (tamedDrift (1 / 2) l b) (tamedDiffusion (1 / 2) l σ) n (Xₙ n)) :
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
      (⨆ t ∈ Set.Icc (0 : ℝ≥0) T, ∫⁻ ω, ‖X t ω - Xₙ n t ω‖ₑ ^ p ∂P)
        ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-(p / 2))) := by sorry

end SabanisEuler.Rate
