-- Prove2me | Theorems.Thm_RobustSpecClust_Est_eq_E11
-- name    : RobustSpecClust.Est.eq_E11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T09:43:38.148669+00:00
-- url     : https://prove2.me/theorems/ace198c8-ce6b-4f0b-a82c-0c49f529c6bd
-- title:
--   (E.11), p. 41 — Bernstein inequality for one-sample U-statistics of degree 2 with an indicator kernel
-- statement:
--   There are constants $c_1, c_2 > 0$ such that the following holds. Let $N \ge 2$ and let $W_1, \dots, W_N$ be independent, identically distributed random elements of a measurable space $\alpha$. Let $S \subseteq \alpha\times\alpha$ be a measurable symmetric set, $p = \mathbb P((W_1, W_2) \in S)$, and
--   $$U = \frac{\#\{(i,j) : i < j,\ (W_i, W_j) \in S\}}{N(N-1)/2}.$$
--   Then for every $t > 0$,
--   $$\mathbb P(U - p > t) \le \exp\Big(-\frac{(N/2)\,t^2}{c_1\,\nu + c_2\,t}\Big), \qquad \nu = p(1-p).$$
--
--   $\nu$ is the variance of the indicator $\mathbb 1\{(W_i,W_j)\in S\}$. This is the Bernstein inequality for one-sample U-statistics (Hoeffding 1963; Arcones 1995) that the paper applies to $U_{kk}$, the fraction of corrupted pairs in the $k$-th diagonal block.
--
--   **Formalization Note** The constants are universal: quantified before $N$, the space and the sample. The kernel is the indicator of a symmetric measurable set, which covers $\mathbb 1\{K_{ij} < \tau_{\mathrm{in}}\}$; the variance is written explicitly as $p(1-p)$.
-- source:
--   arXiv:1912.07546v3, Appendix E, display (E.11), p. 41; Hoeffding (1963), Arcones (1995)

import Mathlib
import Definitions.Def_RobustSpecClust_Est_Setting
open MeasureTheory ProbabilityTheory
open Classical

namespace RobustSpecClust.Est

theorem eq_E11 : ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
    ∀ (N : ℕ) (hN : 2 ≤ N) {α : Type} [MeasurableSpace α] {Ω : Type} [MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P] (W : Fin N → Ω → α),
      (∀ i, Measurable (W i)) → iIndepFun W P → (∀ i j, IdentDistrib (W i) (W j) P P) →
      ∀ S : Set (α × α), MeasurableSet S → (∀ a b, (a, b) ∈ S ↔ (b, a) ∈ S) →
      let p := (P {ω | (W ⟨0, by omega⟩ ω, W ⟨1, by omega⟩ ω) ∈ S}).toReal
      let U : Ω → ℝ := fun ω =>
        ((Finset.univ.filter (fun q : Fin N × Fin N => q.1 < q.2 ∧ (W q.1 ω, W q.2 ω) ∈ S)).card : ℝ) /
          ((N : ℝ) * ((N : ℝ) - 1) / 2)
      ∀ t : ℝ, 0 < t →
        P {ω | t < U ω - p} ≤
          ENNReal.ofReal (Real.exp (-(((N : ℝ) / 2) * t ^ 2) / (c₁ * (p * (1 - p)) + c₂ * t))) := by sorry

end RobustSpecClust.Est
