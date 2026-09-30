-- Prove2me | Theorems.Thm_UnderstandingML_binary_uc_optimal_rate
-- name    : UnderstandingML.binary_uc_optimal_rate
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-25T22:51:18.075091+00:00
-- url     : https://prove2.me/theorems/4c0201c4-ee8a-47ec-9a3f-15a04a617293
-- title:
--   Uniform convergence for VC classes at the optimal rate $(d+\log(1/\delta))/\varepsilon^2$
-- statement:
--   There is an absolute constant $C>0$ such that the following holds. Let $H$ be a class of measurable functions $X \to \{0,1\}$ with the countable-approximation property (a countable subclass approximates every member pointwise, Remark 3.1) and VC dimension at most $d$, where $d \ge 1$. Then $H$ has the uniform convergence property for the $0$–$1$ loss with sample complexity
--   $$m^{UC}_H(\varepsilon,\delta) \le \left\lceil C\,\frac{d + \log(1/\delta)}{\varepsilon^2}\right\rceil,$$
--   i.e. for all $\varepsilon,\delta\in(0,1)$, every distribution $\mathcal D$ over $X\times\{0,1\}$ and every $m$ at least this bound, with probability at least $1-\delta$ over $S\sim\mathcal D^m$ we have $|L_S(h)-L_{\mathcal D}(h)|\le\varepsilon$ for all $h\in H$. This is the upper bound of Theorem 6.8 (part 1) of Shalev-Shwartz and Ben-David without the $\log(1/\varepsilon)$ factor; it requires chaining together with Haussler's packing bound. It is used to derive the multiclass uniform-convergence bound of Theorem 29.3.
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, Theorem 6.8 (p. 48), part 1, upper bound m^UC_H(eps,delta) <= C2 (d + log(1/delta))/eps^2.

import Definitions.Def_UnderstandingML_VC

open MeasureTheory

universe u

namespace UnderstandingML

/-- **Theorem 6.8, part 1 (uniform convergence upper bound, optimal rate)** (p. 48). There is an
absolute constant `C > 0` such that every class `H` of measurable binary classifiers with the
countable-approximation property and VC dimension at most `d` (`d ≥ 1`) has the uniform
convergence property for the 0–1 loss with `m^{UC}_H(ε, δ) ≤ ⌈C (d + log(1/δ))/ε²⌉`. -/
theorem binary_uc_optimal_rate :
    ∃ C : ℝ, 0 < C ∧
      ∀ {X : Type u} [MeasurableSpace X] (H : Set (X → Bool)) (d : ℕ),
        (∀ h ∈ H, Measurable h) → PointwiseSeparable H → vcDim H ≤ d → 1 ≤ d →
        HasUniformConvergenceWith loss01 H
          (fun ε δ ↦ ⌈C * (d + Real.log (1 / δ)) / ε ^ 2⌉₊) := by sorry

end UnderstandingML
