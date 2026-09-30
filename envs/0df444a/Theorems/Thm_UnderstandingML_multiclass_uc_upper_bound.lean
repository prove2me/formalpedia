-- Prove2me | Theorems.Thm_UnderstandingML_multiclass_uc_upper_bound
-- name    : UnderstandingML.multiclass_uc_upper_bound
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-25T21:38:26.072349+00:00
-- url     : https://prove2.me/theorems/4b6a0c3f-4c3b-4f08-af86-e02da0e99052
-- title:
--   Theorem 29.3(1), upper bound: uniform convergence with $O((d\log k + \log(1/\delta))/\epsilon^2)$ examples
-- statement:
--   This is the upper half of item 1 of the Multiclass Fundamental Theorem.
--
--   Let $X$ be a domain with a $\sigma$-algebra containing all singletons, let $Y$ be a finite label set with $k = |Y|$ (also with measurable singletons), and let $H \subseteq Y^X$ be a class of measurable hypotheses with Natarajan dimension $\operatorname{Ndim}(H) = d$ (Definition 29.2). The loss is the multiclass $0$–$1$ loss $\ell(h,(x,y)) = \mathbb{1}[h(x) \ne y]$. Assume moreover that $H$ is nonempty, has the countable-approximation property (Remark 3.1), and that $d \ge 1$.
--
--   There is an absolute constant $C_2 > 0$ (independent of $X$, $Y$, $H$ and $d$) such that $H$ has the uniform convergence property (Definition 4.3) with sample complexity
--
--   $$m^{UC}_H(\epsilon,\delta) \le \left\lceil C_2\,\frac{d \log k + \log(1/\delta)}{\epsilon^2} \right\rceil .$$
--
--   That is, for all $\epsilon, \delta \in (0,1)$, every probability distribution $\mathcal D$ over $X \times Y$ and every $m$ at least this number, a sample $S \sim \mathcal D^m$ is $\epsilon$-representative for $H$ (Definition 4.1) with probability at least $1-\delta$.
--
--   Together with Corollary 4.4 this gives the agnostic upper bound of item 2 for every ERM learner.
--
--   **Formalization Note** The failure probability is an outer measure under the product law. The restriction $d \ge 1$ is necessary: for $d = 0$ the bound reaches $m = 1$ as $\delta \to 1$, and one example is not $\tfrac14$-representative.
-- source:
--   S. Shalev-Shwartz, S. Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, Chapter 29, Theorem 29.3 (The Multiclass Fundamental Theorem), p. 403, item 1 (upper bound on the uniform-convergence sample complexity)

import Definitions.Def_UnderstandingML_MulticlassLearnability

open MeasureTheory
open scoped InnerProductSpace

universe u v

namespace UnderstandingML

/-- **Theorem 29.3, part 1 (upper bound)** (p. 403). There is an absolute constant `C₂ > 0` such
that every nonempty measurable class `H` of functions from `X` to a finite label set `Y` with the
countable-approximation property and Natarajan dimension `d ≥ 1` has the uniform convergence
property (for the multiclass 0–1 loss) with sample complexity
`m^{UC}_H(ε, δ) ≤ ⌈C₂ (d log |Y| + log(1/δ))/ε²⌉`. -/
theorem multiclass_uc_upper_bound :
    ∃ C₂ : ℝ, 0 < C₂ ∧
      ∀ {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSingletonClass X]
        [MeasurableSpace Y] [MeasurableSingletonClass Y] [Fintype Y]
        (H : Set (X → Y)) (d : ℕ), H.Nonempty → (∀ h ∈ H, Measurable h) →
        NPointwiseSeparable H → ndim H = d → 1 ≤ d →
        HasUniformConvergenceWith lossMulti H (fun ε δ ↦
          ⌈C₂ * (d * Real.log (Fintype.card Y) + Real.log (1 / δ)) / ε ^ 2⌉₊) := by sorry

end UnderstandingML
