-- Prove2me | Theorems.Thm_UnderstandingML_multiclass_realizable_upper_bound
-- name    : UnderstandingML.multiclass_realizable_upper_bound
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-25T21:38:30.746624+00:00
-- url     : https://prove2.me/theorems/adc5205f-f04c-44d3-87de-ec56201fd17e
-- title:
--   Theorem 29.3(3), upper bound: every ERM learns in the realizable case with $O((d\log(kd/\epsilon) + \log(1/\delta))/\epsilon)$ examples
-- statement:
--   This is the upper half of item 3 of the Multiclass Fundamental Theorem.
--
--   Let $X$ be a domain with a $\sigma$-algebra containing all singletons, let $Y$ be a finite label set with $k = |Y|$ (also with measurable singletons), and let $H \subseteq Y^X$ be a class of measurable hypotheses with Natarajan dimension $\operatorname{Ndim}(H) = d$ (Definition 29.2). The loss is the multiclass $0$–$1$ loss $\ell(h,(x,y)) = \mathbb{1}[h(x) \ne y]$. Assume moreover that $H$ is nonempty and has the countable-approximation property (Remark 3.1).
--
--   There is an absolute constant $C_2 > 0$ (independent of $X$, $Y$, $H$ and $d$) such that every ERM learner for $H$ PAC learns $H$ under the realizability assumption with sample complexity
--
--   $$m_H(\epsilon,\delta) \le \left\lceil C_2\,\frac{d \log(kd/\epsilon) + \log(1/\delta)}{\epsilon} \right\rceil .$$
--
--   That is, for all $\epsilon,\delta \in (0,1)$, every probability distribution $\mathcal D$ over $X$, every measurable labeling function $f : X \to Y$ for which some $h^\star \in H$ satisfies $\mathcal D(\{h^\star \ne f\}) = 0$, and every $m$ at least this number, the ERM output $h_S$ on $S \sim (\mathcal D, f)^m$ satisfies $\mathcal D(\{h_S \ne f\}) \le \epsilon$ with probability at least $1-\delta$.
--
--   **Formalization Note** The realizable multiclass PAC property is the mission's `IsMulticlassPACWith`, in the shape of Definition 3.1 with error $\mathcal D(\{h \ne f\})$. For $d = 0$ the term $d\log(kd/\epsilon)$ is $0$.
-- source:
--   S. Shalev-Shwartz, S. Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, Chapter 29, Theorem 29.3 (The Multiclass Fundamental Theorem), p. 403, item 3 (upper bound on the realizable sample complexity)

import Definitions.Def_UnderstandingML_MulticlassLearnability

open MeasureTheory
open scoped InnerProductSpace

universe u v

namespace UnderstandingML

/-- **Theorem 29.3, part 3 (upper bound)** (p. 403). There is an absolute constant `C₂ > 0` such
that for every nonempty measurable class `H` of functions from `X` to a finite label set `Y` with
the countable-approximation property and Natarajan dimension `d`, every ERM learner PAC learns
`H` in the realizable case with sample complexity
`m_H(ε, δ) ≤ ⌈C₂ (d log(|Y| d/ε) + log(1/δ))/ε⌉`. -/
theorem multiclass_realizable_upper_bound :
    ∃ C₂ : ℝ, 0 < C₂ ∧
      ∀ {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSingletonClass X]
        [MeasurableSpace Y] [MeasurableSingletonClass Y] [Fintype Y]
        (H : Set (X → Y)) (d : ℕ), H.Nonempty → (∀ h ∈ H, Measurable h) →
        NPointwiseSeparable H → ndim H = d →
        ∀ A : Learner (X × Y) (X → Y), IsERMLearner lossMulti H A →
          IsMulticlassPACWith H A (fun ε δ ↦
            ⌈C₂ * (d * Real.log (Fintype.card Y * d / ε) + Real.log (1 / δ)) / ε⌉₊) := by sorry

end UnderstandingML
