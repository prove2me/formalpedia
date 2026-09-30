-- Prove2me | Theorems.Thm_UnderstandingML_multiclass_agnostic_lower_bound
-- name    : UnderstandingML.multiclass_agnostic_lower_bound
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-25T21:38:27.772514+00:00
-- url     : https://prove2.me/theorems/91697449-edf0-474c-a969-075530e30586
-- title:
--   Theorem 29.3(2), lower bound: agnostic multiclass learning needs $\Omega((d + \log(1/\delta))/\epsilon^2)$ examples
-- statement:
--   This is the lower half of item 2 of the Multiclass Fundamental Theorem.
--
--   Let $X$ be a domain with a $\sigma$-algebra containing all singletons, let $Y$ be a finite label set with $k = |Y|$ (also with measurable singletons), and let $H \subseteq Y^X$ be a class of measurable hypotheses with Natarajan dimension $\operatorname{Ndim}(H) = d$ (Definition 29.2). The loss is the multiclass $0$–$1$ loss $\ell(h,(x,y)) = \mathbb{1}[h(x) \ne y]$. Assume $d \ge 2$.
--
--   There are absolute constants $C_1, \epsilon_0, \delta_0 > 0$ (independent of $X$, $Y$, $H$ and $d$) such that the following holds. If a learning algorithm $A$ (returning hypotheses in $H$) agnostically PAC learns $H$ (Definition 3.4) with sample-complexity function $m_H$, then
--
--   $$C_1\,\frac{d + \log(1/\delta)}{\epsilon^2} \le m_H(\epsilon,\delta) \qquad \text{for all } 0 < \epsilon < \epsilon_0,\ 0 < \delta < \delta_0 .$$
--
--   The corresponding lower bound on $m^{UC}_H$ in item 1 follows, since uniform convergence with $m^{UC}_H$ makes any ERM learner an agnostic PAC learner with $m^{UC}_H(\epsilon/2,\delta)$ examples.
--
--   **Formalization Note** Agnostic PAC learnability is the generic Definition 3.4 of Mission I, instantiated with the multiclass $0$–$1$ loss; it requires the algorithm's outputs to lie in $H$.
-- source:
--   S. Shalev-Shwartz, S. Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, Chapter 29, Theorem 29.3 (The Multiclass Fundamental Theorem), p. 403, item 2 (lower bound on the agnostic sample complexity)

import Definitions.Def_UnderstandingML_MulticlassLearnability

open MeasureTheory
open scoped InnerProductSpace

universe u v

namespace UnderstandingML

/-- **Theorem 29.3, part 2 (lower bound)** (p. 403). There are absolute constants
`C₁, ε₀, δ₀ > 0` such that for every measurable class `H` of functions from `X` to a finite label
set `Y` with Natarajan dimension `d ≥ 2`, every learner `A` and every sample-complexity function
`m_H` with which `A` agnostically PAC learns `H` (multiclass 0–1 loss) satisfy
`C₁ (d + log(1/δ))/ε² ≤ m_H(ε, δ)` whenever `0 < ε < ε₀` and `0 < δ < δ₀`. -/
theorem multiclass_agnostic_lower_bound :
    ∃ C₁ ε₀ δ₀ : ℝ, 0 < C₁ ∧ 0 < ε₀ ∧ 0 < δ₀ ∧
      ∀ {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSingletonClass X]
        [MeasurableSpace Y] [MeasurableSingletonClass Y] [Fintype Y]
        (H : Set (X → Y)) (d : ℕ), (∀ h ∈ H, Measurable h) → ndim H = d → 2 ≤ d →
        ∀ (A : Learner (X × Y) (X → Y)) (mH : ℝ → ℝ → ℕ), IsAgnosticPACWith lossMulti H A mH →
          ∀ ε δ : ℝ, 0 < ε → ε < ε₀ → 0 < δ → δ < δ₀ →
            C₁ * (d + Real.log (1 / δ)) / ε ^ 2 ≤ mH ε δ := by sorry

end UnderstandingML
