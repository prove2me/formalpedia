-- Prove2me | Theorems.Thm_ShockCBM_ControlLimit_proposition_1
-- name    : ShockCBM.ControlLimit.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:17:39.907184+00:00
-- url     : https://prove2.me/theorems/c6c8bbfc-c905-49ba-93af-37beed39c5e4
-- title:
--   Proposition 1, p. 10 — after one period's signal (k, y) the posterior of (Λ, Φ) is Gamma(α + k, β + 1) × conjugate(a + z, b + k)
-- statement:
--   Let $h\ge 0$ generate a natural exponential family on $\mathbb N$ with log-partition $A$ and natural parameter space $\Theta$. Let $\alpha,\beta,a,b>0$, and suppose the conjugate kernel $e^{a\phi-bA(\phi)}$ is integrable on $\Theta$ with positive integral. Take a prior $\Lambda\sim\mathrm{Gamma}(\alpha,\beta)$ (shape $\alpha$, rate $\beta$) independent of $\Phi\sim f_\Phi(\cdot\mid a,b)$, and observe one period's signal $\theta=(k,y)$: $k$ shocks with damages $y_1,\dots,y_k\in\mathbb N$, each with $h(y_i)>0$, and total damage $z=\sum_{i=1}^k y_i$. Then for every $\lambda,\phi\in\mathbb R$ the Bayes posterior density satisfies
--   $$f_{\Lambda,\Phi}(\lambda,\phi\mid\theta)=f_\Lambda(\lambda\mid\alpha+k,\beta+1)\cdot f_\Phi(\phi\mid a+z,b+k).$$
--
--   The posterior thus remains a product of a Gamma density and a conjugate density, with hyperparameters updated by the signal. Iterating it gives the state collapse of the paper: after age $t$ with $n$ shocks and total damage $x$ the hyperparameters are $(\alpha_0+n,\beta_0+t,a_0+x,b_0+n)$.
--
--   **Formalization Note** The posterior is the Bayes formula (likelihood times prior over its integral on $\mathbb R^2$), not the right-hand side. The hypothesis $h(y_i)>0$ excludes impossible observations, for which the posterior is $0/0$. The identity is stated for all $(\lambda,\phi)$, including $\lambda\le 0$ and $\phi\notin\Theta$ where both sides are given by the same Lean conventions (the Gamma density's formula at $0$, the indicator of $\Theta$).
-- source:
--   Drent, Drent, Arts, Kapodistria, Real-Time Integrated Learning and Decision Making for Cumulative Shock Degradation, Manufacturing & Service Operations Management 25(1) (2023), doi:10.1287/msom.2022.1149, accepted manuscript, p. 10, Proposition 1 (proof p. 30, (14))

import Mathlib
import Definitions.Def_ShockCBM_ControlLimit_NEF
import Definitions.Def_ShockCBM_ControlLimit_Setting

namespace ShockCBM.ControlLimit

theorem proposition_1 (h : ℕ → ℝ) (hh : ∀ y, 0 ≤ h y) (α β a b : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (ha : 0 < a) (hb : 0 < b) (hab : ConjNormalizable h a b) (k : ℕ) (y : Fin k → ℕ)
    (hy : ∀ i, 0 < h (y i)) (lam φ : ℝ) :
    posterior h α β a b k y lam φ =
      ProbabilityTheory.gammaPDFReal (α + k) (β + 1) lam *
        conjDensity h (a + ∑ i, (y i : ℝ)) (b + k) φ := by sorry

end ShockCBM.ControlLimit
