-- Prove2me | Theorems.Thm_RiskPremiaDMP_Equivalence_surplus_characterization
-- name    : RiskPremiaDMP.Equivalence.surplus_characterization
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T05:12:01.985439+00:00
-- url     : https://prove2.me/theorems/cebb8b4a-1dad-4efa-bbbb-1fca6040c978
-- title:
--   §2.1, p. 8 (PDF 9), (6)–(8) — Nash split and free entry reduce the value-function PDEs (4) to the surplus PDE (8) and the wage formula
-- statement:
--   Consider the economy without risk premia with parameters $r_f,s,\beta,c,z,\kappa_y,\sigma_y,\kappa_\mu,\sigma_\mu$ satisfying $\kappa_y>0$, $\kappa_\mu\ge0$, $\sigma_\mu\ge0$, $\beta\in(0,1)$, a vacancy-filling rate $q$, and job-finding rate $f(\theta)=\theta q(\theta)$. Let $J,V,W,U$ (values of a filled vacancy, an unfilled vacancy, employment, unemployment), a wage $w$ and a tightness $\theta$ be functions of the state $(y,\mu)$, with $J,W,U$ twice continuously differentiable, solving the PDE system (4)
--   $$\begin{aligned}r_fJ&=e^y-w+\mathscr L^{\mathcal P}J+s(V-J),\\ r_fV&=-c+\mathscr L^{\mathcal P}V+q(\theta)(J-V),\\ r_fW&=w+\mathscr L^{\mathcal P}W+s(U-W),\\ r_fU&=z+\mathscr L^{\mathcal P}U+f(\theta)(W-U),\end{aligned}$$
--   with free entry $V\equiv0$ and the Nash split of the surplus $S=J-V+W-U$ (7): $J-V=(1-\beta)S$ and $W-U=\beta S$. Then $(S,\theta)$ is an equilibrium in the sense of (8),
--   $$(r_f+s)S=e^y-z-\frac{\beta c}{1-\beta}\theta+\mathscr L^{\mathcal P}S,\qquad c=(1-\beta)q(\theta)S,$$
--   and wages equal $w=\beta e^y+(1-\beta)z+\beta c\,\theta$.
--
--   This is the reduction of the four value functions to a single PDE for the match surplus; it gives the equilibrium notion of §2.1 that the artificial economy of Proposition 1 is measured against.
--
--   **Formalization Note** Regularity of $J,W,U$ is an added hypothesis: the generator is computed with `deriv`, which is linear only on differentiable functions.
-- source:
--   Mitra, Seo & Xu, High Discounts and Low Fundamental Surplus, FRB Atlanta Working Paper 2021-22 (Sept. 2021), pp. 7–8 (PDF 8–9), §2.1, (4), (6), (7), (8a)–(8b)

import Mathlib
import Definitions.Def_RiskPremiaDMP_Equivalence_Model

namespace RiskPremiaDMP.Equivalence

theorem surplus_characterization (E : NoRPParams) (hE : E.Standing) (q : ℝ → ℝ)
    (J V W U w θ : ℝ → ℝ → ℝ)
    (hJ : ContDiff ℝ 2 (Function.uncurry J)) (hW : ContDiff ℝ 2 (Function.uncurry W))
    (hU : ContDiff ℝ 2 (Function.uncurry U))
    (h4a : ∀ y μ : ℝ, E.rf * J y μ
      = Real.exp y - w y μ + genP E.κy E.σy E.κμ E.σμ J y μ + E.s * (V y μ - J y μ))
    (h4b : ∀ y μ : ℝ, E.rf * V y μ
      = -E.c + genP E.κy E.σy E.κμ E.σμ V y μ + q (θ y μ) * (J y μ - V y μ))
    (h4c : ∀ y μ : ℝ, E.rf * W y μ
      = w y μ + genP E.κy E.σy E.κμ E.σμ W y μ + E.s * (U y μ - W y μ))
    (h4d : ∀ y μ : ℝ, E.rf * U y μ
      = E.z + genP E.κy E.σy E.κμ E.σμ U y μ + θ y μ * q (θ y μ) * (W y μ - U y μ))
    (hfree : ∀ y μ : ℝ, V y μ = 0)
    (hfirm : ∀ y μ : ℝ, J y μ - V y μ = (1 - E.β) * (J y μ - V y μ + W y μ - U y μ))
    (hworker : ∀ y μ : ℝ, W y μ - U y μ = E.β * (J y μ - V y μ + W y μ - U y μ)) :
    IsEquilibriumNoRP E q (fun y μ => J y μ - V y μ + W y μ - U y μ) θ ∧
      ∀ y μ : ℝ, w y μ = E.β * Real.exp y + (1 - E.β) * E.z + E.β * E.c * θ y μ := by sorry

end RiskPremiaDMP.Equivalence
