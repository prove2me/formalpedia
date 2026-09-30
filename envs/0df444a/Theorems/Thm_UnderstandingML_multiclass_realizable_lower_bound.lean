-- Prove2me | Theorems.Thm_UnderstandingML_multiclass_realizable_lower_bound
-- name    : UnderstandingML.multiclass_realizable_lower_bound
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-25T21:38:26.025814+00:00
-- url     : https://prove2.me/theorems/4bfba328-c55a-4f11-ab18-9bdd3616cd1d
-- title:
--   Theorem 29.3(3), lower bound: realizable multiclass learning needs $\Omega((d + \log(1/\delta))/\epsilon)$ examples
-- statement:
--   This is the lower half of item 3 of the Multiclass Fundamental Theorem.
--
--   Let $X$ be a domain with a $\sigma$-algebra containing all singletons, let $Y$ be a finite label set with $k = |Y|$ (also with measurable singletons), and let $H \subseteq Y^X$ be a class of measurable hypotheses with Natarajan dimension $\operatorname{Ndim}(H) = d$ (Definition 29.2). The loss is the multiclass $0$–$1$ loss $\ell(h,(x,y)) = \mathbb{1}[h(x) \ne y]$. Assume $d \ge 2$.
--
--   There are absolute constants $C_1, \epsilon_0, \delta_0 > 0$ (independent of $X$, $Y$, $H$ and $d$) such that the following holds. If a learning algorithm $A$ PAC learns $H$ under the realizability assumption with sample-complexity function $m_H$, then
--
--   $$C_1\,\frac{d + \log(1/\delta)}{\epsilon} \le m_H(\epsilon,\delta) \qquad \text{for all } 0 < \epsilon < \epsilon_0,\ 0 < \delta < \delta_0 .$$
--
--   **Formalization Note** The realizable multiclass PAC property is the mission's `IsMulticlassPACWith` (Definition 3.1 with error $\mathcal D(\{h \ne f\})$ for a measurable target $f$ that agrees $\mathcal D$-almost surely with some $h^\star \in H$); the algorithm may be improper.
-- source:
--   S. Shalev-Shwartz, S. Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, Chapter 29, Theorem 29.3 (The Multiclass Fundamental Theorem), p. 403, item 3 (lower bound on the realizable sample complexity)

import Definitions.Def_UnderstandingML_MulticlassLearnability

open MeasureTheory
open scoped InnerProductSpace

universe u v

namespace UnderstandingML

/-- **Theorem 29.3, part 3 (lower bound)** (p. 403). There are absolute constants
`C₁, ε₀, δ₀ > 0` such that for every measurable class `H` of functions from `X` to a finite label
set `Y` with Natarajan dimension `d ≥ 2`, every learner `A` and every sample-complexity function
`m_H` with which `A` PAC learns `H` in the realizable case satisfy
`C₁ (d + log(1/δ))/ε ≤ m_H(ε, δ)` whenever `0 < ε < ε₀` and `0 < δ < δ₀`. -/
theorem multiclass_realizable_lower_bound :
    ∃ C₁ ε₀ δ₀ : ℝ, 0 < C₁ ∧ 0 < ε₀ ∧ 0 < δ₀ ∧
      ∀ {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSingletonClass X]
        [MeasurableSpace Y] [MeasurableSingletonClass Y] [Fintype Y]
        (H : Set (X → Y)) (d : ℕ), (∀ h ∈ H, Measurable h) → ndim H = d → 2 ≤ d →
        ∀ (A : Learner (X × Y) (X → Y)) (mH : ℝ → ℝ → ℕ), IsMulticlassPACWith H A mH →
          ∀ ε δ : ℝ, 0 < ε → ε < ε₀ → 0 < δ → δ < δ₀ →
            C₁ * (d + Real.log (1 / δ)) / ε ≤ mH ε δ := by sorry

end UnderstandingML
