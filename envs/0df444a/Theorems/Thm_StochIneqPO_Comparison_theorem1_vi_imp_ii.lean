-- Prove2me | Theorems.Thm_StochIneqPO_Comparison_theorem1_vi_imp_ii
-- name    : StochIneqPO.Comparison.theorem1_vi_imp_ii
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-11-06T17:47:54.551893+00:00
-- url     : https://prove2.me/theorems/7e5b3fef-6b5c-406d-af5d-ba31be033e9b
-- title:
--   Theorem 1 (vi) ⇒ (ii), p. 900 — closed increasing sets ordered give a coupling supported on $\{x \le y\}$ (Strassen)
-- statement:
--   Let $E$ be a partially ordered Polish space (the order is closed, i.e. $\{(x,y) : x \le y\}$ is a closed subset of $E \times E$, and $E$ carries its Borel $\sigma$-algebra), and let $P_1, P_2$ be probability measures on $E$. Suppose that
--   $$P_1(B) \le P_2(B) \qquad \text{for every closed increasing set } B \subseteq E.$$
--   Then there exists a probability measure $\lambda$ on $E \times E$ with support in $K = \{(x,y) \in E \times E : x \le y\}$ (that is, $\lambda(K^{c}) = 0$), with first marginal $P_1$ and second marginal $P_2$.
--
--   This is the implication (vi) $\Rightarrow$ (ii) of Theorem 1 of Kamae–Krengel–O'Brien, which the paper obtains from Strassen's theorem (1965) on the existence of probability measures with given marginals supported by a closed set. It is the only nonelementary step of Theorem 1: the remaining implications (i) $\Rightarrow$ (vi) $\Rightarrow$ (ii) $\Rightarrow$ (iii) $\Rightarrow$ (iv) $\Rightarrow$ (i) and (ii) $\Leftrightarrow$ (v) are routine.
--
--   **Formalization Note** The hypotheses are exactly condition (vi) of the milestone `StochIneqPO.Comparison.theorem1_tfae`, and the conclusion is exactly its condition (ii), with the same encoding: "partially ordered Polish space" is `[PolishSpace E] [BorelSpace E] [PartialOrder E] [OrderClosedTopology E]`, "support in $K$" is $\lambda(K^{c}) = 0$, and the marginals are the images under `Prod.fst` and `Prod.snd`.
-- source:
--   Kamae, Krengel, O'Brien, Stochastic Inequalities on Partially Ordered Spaces, Ann. Probab. 5 (1977), Theorem 1, implication (vi) ⇒ (ii), p. 900 (via Strassen 1965, Ann. Math. Statist. 36, Theorem 11)

import Mathlib

namespace StochIneqPO.Comparison

open MeasureTheory ProbabilityTheory

theorem theorem1_vi_imp_ii {E : Type*} [TopologicalSpace E] [PolishSpace E] [MeasurableSpace E]
    [BorelSpace E] [PartialOrder E] [OrderClosedTopology E]
    (P₁ P₂ : Measure E) [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂]
    (h : ∀ B : Set E, IsClosed B → IsUpperSet B → P₁ B ≤ P₂ B) :
    ∃ lam : Measure (E × E), IsProbabilityMeasure lam ∧ lam {z : E × E | z.1 ≤ z.2}ᶜ = 0 ∧
      lam.map Prod.fst = P₁ ∧ lam.map Prod.snd = P₂ := by sorry

end StochIneqPO.Comparison
