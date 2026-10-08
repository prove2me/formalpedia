-- Prove2me | Theorems.Thm_ProbMetricStab_Portfolio_lemma_5_1_b
-- name    : ProbMetricStab.Portfolio.lemma_5_1_b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T23:04:52.767227+00:00
-- url     : https://prove2.me/theorems/77a343be-1e39-45ba-b497-fdc83d00bcb3
-- title:
--   Lemma 5.1, second assertion, p. 24 — S(α, Γ) ≠ ∅ and ¼α(α − 1)∫|⟨x − x_*, z⟩|²Γ(dz) ≤ r_{α,Γ}(x) − v(α, Γ)
-- statement:
--   Let $\alpha\in(1,2)$ and let $\Gamma$ be a Borel probability measure on the unit sphere $\Sigma^s\subset\mathbb R^s$. Let $r_{\alpha,\Gamma}(x)=\int_{\Sigma^s}|\langle x,\xi\rangle|^\alpha\Gamma(d\xi)$, let $X$ be the standard simplex, and let $v(\alpha,\Gamma)$ and $S(\alpha,\Gamma)$ be the optimal value and the solution set of $\min_{x\in X}r_{\alpha,\Gamma}(x)$. Then $S(\alpha,\Gamma)\neq\emptyset$, and there is $x_*\in S(\alpha,\Gamma)$ such that for all $x\in X$
--   $$\tfrac14\,\alpha(\alpha-1)\int_{\Sigma^s}|\langle x-x_*,z\rangle|^2\,\Gamma(dz)\le r_{\alpha,\Gamma}(x)-v(\alpha,\Gamma).$$
--
--   This quadratic growth condition controls how fast the risk increases away from the solution set; it is the growth function that enters the stability modulus $\Psi$ of Theorem 5.2.
--
--   **Formalization Note** As printed, the growth estimate is claimed for some $x_*\in S(\alpha,\Gamma)$ (an existential), not for every minimizer.
-- source:
--   Rachev & Römisch, Quantitative stability in stochastic programming: The method of probability metrics, preprint (edoc.hu-berlin.de), p. 24, Lemma 5.1 (second sentence)

import Mathlib
import Definitions.Def_ProbMetricStab_Portfolio_Setting

open MeasureTheory
open scoped ENNReal

namespace ProbMetricStab.Portfolio
theorem lemma_5_1_b {s : ℕ} (α : ℝ) (hα1 : 1 < α) (hα2 : α < 2) (Γ : Measure (Rs s))
    (hΓ : IsSpectral Γ) :
    (solSet α Γ).Nonempty ∧
    ∃ xs ∈ solSet α Γ, ∀ x ∈ simplex s,
      (1 / 4) * α * (α - 1) * (∫ z in unitSphere s, |(inner ℝ (x - xs) z : ℝ)| ^ 2 ∂Γ)
        ≤ risk α Γ x - optVal α Γ := by sorry
end ProbMetricStab.Portfolio
