-- Prove2me | Theorems.Thm_ShockCBM_ControlLimit_lemma_1
-- name    : ShockCBM.ControlLimit.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:17:34.275806+00:00
-- url     : https://prove2.me/theorems/be36ea36-e84b-456e-8d4d-e0b732e9559a
-- title:
--   Lemma 1, p. 11 — the posterior predictive law of Z_(t,t+1] is the negative-binomial mixture (6) of k-fold convolutions
-- statement:
--   Let $h$ generate a natural exponential family on $\mathbb N$ with natural parameter space $\Theta$, and let $\alpha,\beta,a,b>0$. Under independent $\Lambda\sim\mathrm{Gamma}(\alpha,\beta)$ (rate $\beta$) and $\Phi\sim f_\Phi(\cdot\mid a,b)$, the predictive probability that the next period's damage equals $z\in\mathbb N$ is
--   $$\mathbb P[Z=z\mid\alpha,\beta,a,b]=\sum_{k=0}^{\infty}\int_\Theta f^{(k)}(z\mid\phi)f_\Phi(\phi\mid a,b)\,d\phi\ \binom{k+\alpha-1}{k}\Big(\frac1{\beta+1}\Big)^{k}\Big(\frac{\beta}{\beta+1}\Big)^{\alpha},$$
--   where $f^{(k)}$ is the $k$-fold convolution of the damage pmf and the left-hand side is $\sum_k\mathbb P[Z=z,K=k]$ for the predictive kernel defined by the Poisson–Gamma and convolution–conjugate integrals.
--
--   The lemma identifies the law of the shock count $K$ as negative binomial with $r=\alpha$ and $p=1/(\beta+1)$, which gives the closed-form predictive law used for computation.
--
--   **Formalization Note** For real $\alpha$ the generalized binomial coefficient is written $\Gamma(k+\alpha)/(k!\,\Gamma(\alpha))$, and $(\beta/(\beta+1))^\alpha$ is a real power. The paper prints the $\phi$-integral over $(-\infty,\infty)$ (and over $(0,\infty)$ in its proof); it is taken over $\Theta$, the support of the conjugate prior. This agrees with the printed $(-\infty,\infty)$ integral because the conjugate density vanishes off $\Theta$, whereas $(0,\infty)$ would be wrong for families such as the geometric, whose $\Theta$ is $(-\infty,0)$.
-- source:
--   Drent, Drent, Arts, Kapodistria, Real-Time Integrated Learning and Decision Making for Cumulative Shock Degradation, Manufacturing & Service Operations Management 25(1) (2023), doi:10.1287/msom.2022.1149, accepted manuscript, p. 11, Lemma 1, (6) (proof p. 30, (15)–(16))

import Mathlib
import Definitions.Def_ShockCBM_ControlLimit_NEF
import Definitions.Def_ShockCBM_ControlLimit_Setting

namespace ShockCBM.ControlLimit

theorem lemma_1 (h : ℕ → ℝ) (α β a b : ℝ) (hα : 0 < α) (hβ : 0 < β) (ha : 0 < a) (hb : 0 < b)
    (z : ℕ) :
    ∑' k : ℕ, predKernel h α β a b z k =
      ∑' k : ℕ, damagePart h a b k z *
        (Real.Gamma ((k : ℝ) + α) / ((Nat.factorial k : ℝ) * Real.Gamma α)) *
        (1 / (β + 1)) ^ k * (β / (β + 1)) ^ α := by sorry

end ShockCBM.ControlLimit
