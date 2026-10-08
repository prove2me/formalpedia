-- Prove2me | Theorems.Thm_ProbMetricStab_Portfolio_risk_lipschitz
-- name    : ProbMetricStab.Portfolio.risk_lipschitz
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T23:04:55.860684+00:00
-- url     : https://prove2.me/theorems/a205a6bf-d3e1-493f-a321-ab0b9460e15d
-- title:
--   Proof of Theorem 5.2, p. 25 — |r_{α,Γ}(x) − r_{α̃,Γ̃}(x)| ≤ αζ₁(Γ, Γ̃) + e⁻¹|α − α̃| on X
-- statement:
--   Let $\alpha,\tilde\alpha\in(1,2)$ and let $\Gamma,\tilde\Gamma$ be Borel probability measures on the unit sphere $\Sigma^s$. With $r_{\alpha,\Gamma}(x)=\int_{\Sigma^s}|\langle x,\xi\rangle|^\alpha\Gamma(d\xi)$, $X$ the standard simplex and $\zeta_1$ the dual Lipschitz metric on $\Sigma^s$, for every $x\in X$
--   $$|r_{\alpha,\Gamma}(x)-r_{\tilde\alpha,\tilde\Gamma}(x)|\le\alpha\,\zeta_1(\Gamma,\tilde\Gamma)+e^{-1}|\alpha-\tilde\alpha|,\qquad e=\exp(1).$$
--
--   The risk is thus jointly Lipschitz in the stability index and the spectral measure, uniformly on $X$; together with the growth condition of Lemma 5.1 this is what Theorem 5.2 needs.
--
--   **Formalization Note** Both sides are compared in $[0,\infty]$ because $\zeta_1$ is defined as a supremum in $[0,\infty]$; it is finite (at most $2$), so the inequality is the real one.
-- source:
--   Rachev & Römisch, Quantitative stability in stochastic programming: The method of probability metrics, preprint (edoc.hu-berlin.de), p. 25, proof of Theorem 5.2, first display (outer inequality)

import Mathlib
import Definitions.Def_ProbMetricStab_Portfolio_Setting

open MeasureTheory
open scoped ENNReal

namespace ProbMetricStab.Portfolio
theorem risk_lipschitz {s : ℕ} (α α' : ℝ) (hα1 : 1 < α) (hα2 : α < 2) (hα'1 : 1 < α')
    (hα'2 : α' < 2) (Γ Γ' : Measure (Rs s)) (hΓ : IsSpectral Γ) (hΓ' : IsSpectral Γ')
    (x : Rs s) (hx : x ∈ simplex s) :
    ENNReal.ofReal |risk α Γ x - risk α' Γ' x|
      ≤ ENNReal.ofReal α * zeta1 Γ Γ' + ENNReal.ofReal (Real.exp (-1) * |α - α'|) := by sorry
end ProbMetricStab.Portfolio
