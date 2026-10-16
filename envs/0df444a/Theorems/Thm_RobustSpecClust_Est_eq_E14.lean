-- Prove2me | Theorems.Thm_RobustSpecClust_Est_eq_E14
-- name    : RobustSpecClust.Est.eq_E14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T09:43:39.750544+00:00
-- url     : https://prove2.me/theorems/3d64e61e-ad9f-4019-9898-93d05b64c409
-- title:
--   (E.14), p. 42 — Bernstein inequality for two-sample U-statistics with an indicator kernel
-- statement:
--   There are constants $c_4, c_5 > 0$ such that the following holds. Let $N_1, N_2 \ge 1$ and let $V_1,\dots,V_{N_1}, W_1,\dots,W_{N_2}$ be mutually independent random elements of a measurable space $\alpha$, with the $V_i$ identically distributed and the $W_j$ identically distributed. Let $S \subseteq \alpha\times\alpha$ be measurable, $p = \mathbb P((V_1, W_1) \in S)$, and
--   $$U = \frac{\#\{(i,j) : (V_i, W_j) \in S\}}{N_1 N_2}.$$
--   Then for every $t > 0$,
--   $$\mathbb P(U - p > t) \le \exp\Big(-\frac{\min\{N_1,N_2\}\,t^2}{c_4\,\nu + c_5\,t}\Big), \qquad \nu = p(1-p).$$
--
--   This is the two-sample analogue of (E.11), which the paper derives "following the arguments" of Pitcan (2017) and Hoeffding (1963, §5b); it is applied to $U_{kl}$, the fraction of corrupted entries of the off-diagonal block $(k,l)$.
--
--   **Formalization Note** The constants are universal. Both samples take values in the same space (in the paper, $\mathbb R^d$); independence is one `iIndepFun` over the disjoint union of the two index sets.
-- source:
--   arXiv:1912.07546v3, Appendix E, display (E.14), p. 42; Hoeffding (1963), §5b; Pitcan (2017)

import Mathlib
import Definitions.Def_RobustSpecClust_Est_Setting
open MeasureTheory ProbabilityTheory
open Classical

namespace RobustSpecClust.Est

theorem eq_E14 : ∃ c₄ c₅ : ℝ, 0 < c₄ ∧ 0 < c₅ ∧
    ∀ (N₁ N₂ : ℕ) (h₁ : 1 ≤ N₁) (h₂ : 1 ≤ N₂) {α : Type} [MeasurableSpace α] {Ω : Type}
      [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (V : Fin N₁ → Ω → α) (W : Fin N₂ → Ω → α),
      (∀ i, Measurable (V i)) → (∀ j, Measurable (W j)) → iIndepFun (Sum.elim V W) P →
      (∀ i i', IdentDistrib (V i) (V i') P P) → (∀ j j', IdentDistrib (W j) (W j') P P) →
      ∀ S : Set (α × α), MeasurableSet S →
      let p := (P {ω | (V ⟨0, by omega⟩ ω, W ⟨0, by omega⟩ ω) ∈ S}).toReal
      let U : Ω → ℝ := fun ω =>
        ((Finset.univ.filter (fun q : Fin N₁ × Fin N₂ => (V q.1 ω, W q.2 ω) ∈ S)).card : ℝ) /
          ((N₁ : ℝ) * N₂)
      ∀ t : ℝ, 0 < t →
        P {ω | t < U ω - p} ≤
          ENNReal.ofReal (Real.exp (-((min (N₁ : ℝ) N₂) * t ^ 2) / (c₄ * (p * (1 - p)) + c₅ * t))) := by sorry

end RobustSpecClust.Est
