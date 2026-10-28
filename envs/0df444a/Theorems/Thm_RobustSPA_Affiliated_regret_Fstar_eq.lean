-- Prove2me | Theorems.Thm_RobustSPA_Affiliated_regret_Fstar_eq
-- name    : RobustSPA.Affiliated.regret_Fstar_eq
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-24T09:06:48.50616+00:00
-- url     : https://prove2.me/theorems/ef461806-f54e-44a1-9e04-256e9363ccc0
-- title:
--   Proof of Proposition 2, p. 21 — R_n(Φ*_n, F*_n) = r*_n + ∫_{r*_n}^1 (bracket at z = F*_n(p)^n) Φ*_n(p) dp
-- statement:
--   Fix $n\ge1$ buyers. Let $r=r^*_n\in(0,1/n)$ solve the $r^*$-equation
--   $$(1-r)^{n-1}+\log r+\sum_{k=1}^{n-1}\frac{(1-r)^k}{k}=0,$$
--   let $\rho$ be a probability law on $\mathbb R$ with CDF $\Phi^*_n$ (Theorem 1), and let $G$ be a probability law on $\mathbb R$ with the isorevenue CDF $F^*_n(t)=1-r/t$ on $[r,1)$, $0$ below $r$ and $1$ from $1$ on (F-IsoRevenue). Write $\mathbf F^*_n=G^{\otimes n}$. Then the regret of $\mathrm{SPA}(\Phi^*_n)$ against $\mathbf F^*_n$ is
--   $$R_n(\Phi^*_n,\mathbf F^*_n)= r+\int_{r}^{1}\Big(\frac{(n-1)r}{p-r}-1-\frac{(n-1)p}{p-r}\Big(1-\frac rp\Big)^{n}+n\Big(1-\frac rp\Big)^{n-1}\Big)\Phi^*_n(p)\,dp .$$
--   This is the closing equality of the proof of Proposition 2: the bracket is the expression maximised over $z\in[0,1]$, evaluated at its maximiser $z=F^*_n(p)^n=(1-r/p)^n$, so that the upper bound obtained for every exchangeable affiliated law is exactly the regret at the i.i.d. isorevenue law.
--
--   It follows from (Regret-$F$) of Proposition 1 applied to the i.i.d. law $\mathbf F^*_n$ (for which $\int_0^{r}F^n=0$) together with the identity $F^{(2)}_n=nF^{(1)}_{n-1}-(n-1)F^{(1)}_n$, $F^{(1)}_k=(F^*_n)^k$, and the ODE $(\Phi^*_n)'(p)=1/p-(n-1)r\,\Phi^*_n(p)/(p(p-r))$.
--
--   **Formalization Note.** $r^*_n$, $\Phi^*_n$ and (F-IsoRevenue) enter as hypotheses exactly as in `RobustSPA.Affiliated.proposition_2` and `nature_step_aff`; $n=1$ is included (then the bracket vanishes and the regret is $r^*_1=1/e$). The integral is the interval integral over $[r,1]$; its integrand is bounded there.
-- source:
--   Anunrojwong, Balseiro & Besbes, On the Robustness of Second-Price Auctions in Prior-Independent Mechanism Design, arXiv:2204.10478v5, p. 21, last display of the proof of Proposition 2 (the final equality "$= R_n(\Phi^*_n,\mathbf F^*_n)$"); it is (Regret-$F$) of Proposition 1, p. 16, for the i.i.d. isorevenue law (F-IsoRevenue), p. App-1, after substituting (ODE-$\Phi$)

import Mathlib
import Definitions.Def_RobustSPA_Affiliated_Setting

namespace RobustSPA.Affiliated

open MeasureTheory RobustSPA.IID

theorem regret_Fstar_eq (n : ℕ) (hn : 0 < n) (r : ℝ) (hr : r ∈ Set.Ioo (0 : ℝ) (1 / (n : ℝ)))
    (hrEq : rEq n r = 0) (ρ : ProbabilityMeasure ℝ) (hρ : ∀ t, cdfOf ρ t = PhiStar n r t)
    (G : ProbabilityMeasure ℝ) (hG : ∀ t, cdfOf G t = isoCDF r t) :
    regret (SPA (ρ : Measure ℝ)) (Measure.pi fun _ : Fin n => (G : Measure ℝ)) =
      r + ∫ p in r..1, (((n : ℝ) - 1) * r / (p - r) - 1 -
        ((n : ℝ) - 1) * p / (p - r) * (1 - r / p) ^ n + (n : ℝ) * (1 - r / p) ^ (n - 1)) *
          PhiStar n r p := by sorry

end RobustSPA.Affiliated
