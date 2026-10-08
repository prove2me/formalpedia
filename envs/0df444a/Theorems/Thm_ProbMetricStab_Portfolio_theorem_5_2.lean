-- Prove2me | Theorems.Thm_ProbMetricStab_Portfolio_theorem_5_2
-- name    : ProbMetricStab.Portfolio.theorem_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T23:05:35.651974+00:00
-- url     : https://prove2.me/theorems/c4ef8703-a8fd-4abb-a63c-1791bf58d636
-- title:
--   Theorem 5.2, p. 25 — sup_{x∈S(α̃,Γ̃)} d(x, S(α, Γ)) ≤ Ψ(αζ₁(Γ, Γ̃) + e⁻¹|α − α̃|) for ζ₁(Γ, Γ̃) + |α − α̃| < δ
-- statement:
--   Consider the minimal-risk portfolio problem (22), $\min\{r_{\alpha,\Gamma}(x):x\in X\}$, where $X$ is the standard simplex of $\mathbb R^s$, $\Gamma$ is a Borel probability measure on the unit sphere $\Sigma^s$, and $r_{\alpha,\Gamma}(x)=\int_{\Sigma^s}|\langle x,\xi\rangle|^\alpha\Gamma(d\xi)$. Write $S(\alpha,\Gamma)$ for its solution set, $\zeta_1$ for the dual Lipschitz metric on $\Sigma^s$, $e=\exp(1)$, and $\Psi(\eta)=\eta+\psi^{-1}(2\eta)$, where $\psi$ is the growth function of the unperturbed problem (see the Setting definition).
--
--   **Theorem.** For each $(\alpha,\Gamma)\in(1,2)\times\mathcal P(\Sigma^s)$ there is a constant $\delta>0$ such that
--   $$\sup_{x\in S(\tilde\alpha,\tilde\Gamma)}d\big(x,S(\alpha,\Gamma)\big)\le\Psi\big(\alpha\,\zeta_1(\Gamma,\tilde\Gamma)+e^{-1}|\alpha-\tilde\alpha|\big)$$
--   whenever $(\tilde\alpha,\tilde\Gamma)\in(1,2)\times\mathcal P(\Sigma^s)$ and $\zeta_1(\Gamma,\tilde\Gamma)+|\alpha-\tilde\alpha|<\delta$.
--
--   The optimal portfolios are therefore upper semicontinuous, with an explicit modulus, under simultaneous perturbation of the stability index and of the spectral measure, for instance when both are estimated from data.
--
--   **Formalization Note** The supremum over $S(\tilde\alpha,\tilde\Gamma)$ is stated pointwise for every $x\in S(\tilde\alpha,\tilde\Gamma)$. Distances are extended distances (`Metric.infEDist`), and $\Psi$ takes values in $[0,\infty]$. The smallness condition is stated in $[0,\infty]$ and forces $\zeta_1(\Gamma,\tilde\Gamma)<\infty$, so the argument of $\Psi$ uses the real value of $\zeta_1(\Gamma,\tilde\Gamma)$.
-- source:
--   Rachev & Römisch, Quantitative stability in stochastic programming: The method of probability metrics, preprint (edoc.hu-berlin.de), p. 25, Theorem 5.2 (first assertion)

import Mathlib
import Definitions.Def_ProbMetricStab_Portfolio_Setting

open MeasureTheory
open scoped ENNReal

namespace ProbMetricStab.Portfolio
theorem theorem_5_2 {s : ℕ} (α : ℝ) (hα1 : 1 < α) (hα2 : α < 2) (Γ : Measure (Rs s))
    (hΓ : IsSpectral Γ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (α' : ℝ) (Γ' : Measure (Rs s)), 1 < α' → α' < 2 → IsSpectral Γ' →
      zeta1 Γ Γ' + ENNReal.ofReal |α - α'| < ENNReal.ofReal δ →
      ∀ x ∈ solSet α' Γ',
        Metric.infEDist x (solSet α Γ)
          ≤ Psi α Γ (α * (zeta1 Γ Γ').toReal + Real.exp (-1) * |α - α'|) := by sorry
end ProbMetricStab.Portfolio
