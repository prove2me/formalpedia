-- Prove2me | Theorems.Thm_PrimalDualPricing_Regret_lemma_5
-- name    : PrimalDualPricing.Regret.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:24:27.630642+00:00
-- url     : https://prove2.me/theorems/482852c4-73de-49b7-bb77-e4ca5bc3d783
-- title:
--   Lemma 5, p. 14 — $\mathbb P(\cap_{k=1}^K\{A_k\cap B_k\cap C_k\})=1-O((\log n)^2n^{-1})$
-- statement:
--   Under Assumptions 1–2 and Remark 2, let $A_k$, $B_k$, $C_k$ be the events that the interval estimators of phase $k$ of Algorithm 1 contain $p^*_m$ for all $m$, contain $z^*$, and contain $\mathcal P_m(z)$ for all $m$ and all $z$ in the dual interval. For every sufficiently small $\epsilon>0$ there is a constant $C$, independent of $n$, such that for every $n\ge3$
--   $$\mathbb P\Big(\bigcap_{k=1}^K\{A_k\cap B_k\cap C_k\}\Big)\ge1-\frac{C(\log n)^2}{n}.$$
--
--   At the beginning of the last phase the algorithm has therefore not "gone wrong", except with probability $O((\log n)^2/n)$.
--
--   **Formalization Note** The statement bounds the probability of the complement of the intersection by $C(\log n)^2/n$.
-- source:
--   Chen, Gallego, A Primal-dual Learning Algorithm for Personalized Dynamic Pricing with an Inventory Constraint, arXiv:1812.09234v3, p. 14, Lemma 5

import Mathlib
import Definitions.Def_PrimalDualPricing_Regret_System

namespace PrimalDualPricing.Regret

open MeasureTheory ProbabilityTheory

/-- Lemma 5 (Chen–Gallego, arXiv:1812.09234v3, p. 14): `P(∩_{k=1}^K {A_k ∩ B_k ∩ C_k}) = 1 − O((log n)² n^{−1})`.
Under Assumptions 1–2 and Remark 2, for every sufficiently small `ε > 0` there is `C`, independent of `n`,
such that for every `n ≥ 3` the probability that some event `A_k ∩ B_k ∩ C_k`, `1 ≤ k ≤ K`, fails is at most
`C (log n)² / n`. -/
theorem lemma_5 {M : ℕ} (S : Setting M) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ eps : ℝ, 0 < eps → eps < ε₀ → ∃ C : ℝ,
      ∀ (Ω : Type) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
        (N : Fin M → ℝ → Ω → ℕ), IndepPoissonPaths N →
        ∀ n : ℕ, 3 ≤ n →
          (ℙ (⋂ k ∈ Set.Icc 1 (numPhases eps n),
              S.eventA eps n N k ∩ S.eventB eps n N k ∩ S.eventC eps n N k)ᶜ).toReal
            ≤ C * Real.log n ^ 2 / n := by sorry

end PrimalDualPricing.Regret
