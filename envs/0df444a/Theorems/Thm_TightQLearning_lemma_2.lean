-- Prove2me | Theorems.Thm_TightQLearning_lemma_2
-- name    : TightQLearning.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:33:09.552359+00:00
-- url     : https://prove2.me/theorems/bd32f79f-b31b-4d74-874c-ecc034a59574
-- title:
--   Lemma 2 — the lower half of the recursion for $\Delta_t$
-- statement:
--   There is a universal constant $c_4>0$ such that for all $c_1\ge c_2>0$ with $c_1c_2\le c_4/8$ there is $c_3>0$ with the following property. Let $\gamma,\delta\in(0,1)$, let the rewards lie in $[0,1]$, let $T\ge2$, let the rates obey (16a), let $0\le Q_0\le\frac1{1-\gamma}$, and let
--   $$T\ge\frac{c_3(\log^4T)\big(\log\frac{|\mathcal S||\mathcal A|T}\delta\big)}{(1-\gamma)^3}.$$
--   Then, with probability at least $1-\delta$, simultaneously for all $2\le t\le T$ with $t\ge\frac T{c_2\log T}$,
--   $$\Delta_t\ge-30\sqrt{\frac{(\log^4T)\big(\log\frac{|\mathcal S||\mathcal A|T}\delta\big)}{\gamma^2(1-\gamma)^4T}\Big(1+\max_{t/2\le i<t}\|\Delta_i\|_\infty\Big)}\;\mathbf 1.$$
--
--   Together with Lemma 1 this gives the two-sided recursion (40) for $\|\Delta_t\|_\infty$.
--
--   Differences from the source:
--   - encoding: the state and action spaces are {1,…,|S|} and {1,…,|A|} → finite nonempty types X and A; reason: the instances are the same up to relabelling; |S||A| is Fintype.card X * Fintype.card A
--   - encoding: V^π and Q^π are expectations along a trajectory → the published PolicyValue series, with QFunction for the first step; reason: the series computes the expectation term by term; Q^π is r + γPV^π, the trajectory with a₀ fixed
--   - encoding: samples s_t(s,a) ∼ P(·|s,a), independent, for t = 1,…,T → IsGenerativeModel on an arbitrary probability space: joint independence over (t,s,a) with 1 ≤ t ≤ T, law P(·|s,a), discrete σ-algebra on X; reason: this is the page's sampling model; the algorithm never reads a sample outside that range
--   - encoding: (16a) divides by log³T, which is undefined at T = 1 → the hypothesis 2 ≤ T; reason: it excludes only T = 0 and T = 1, where the printed condition is undefined; Lean's x/0 = 0 would make the statement false there (verified)
--   - encoding: max over t/2 ≤ i < t, which is undefined for t = 1 → the hypothesis 2 ≤ t, and windowMax over a nonempty window; reason: it excludes only the case where the printed maximum is undefined
--   - reading: "Suppose that c₁c₂ ≤ c₄/8" with c₄ "some constant" → ∃ c₄ > 0, ∀ c₁ ≥ c₂ > 0 with c₁c₂ ≤ c₄/8, ∃ c₃ > 0, before every instance quantity; reason: c₃ must follow c₁, c₂ (see theorem_2); c₄ is the constant of (37) that the proof needs small
--   - reading: "for all t ≥ T/(c₂ log T)" → T/(c₂ log T) ≤ t ≤ T; reason: the iterates are constrained only up to T; (91) and p.22 work in this range
--   - generalization: the standing assumption of Appendix B is (59) with ε ≤ 1/(1−γ) → the weaker condition (63), T ≥ c₃ log⁴T log(|S||A|T/δ)/(1−γ)³; reason: the page derives (63) from (59) and the proof uses only (63)
-- source:
--   Li, Cai, Chen, Wei & Chi, Is Q-Learning Minimax Optimal? A Tight Sample Complexity Analysis, arXiv:2102.06548v4 (https://arxiv.org/abs/2102.06548v4), Lemma 2, p.14

import Mathlib
import Definitions.Def_TightQLearning_syncQ
import Definitions.Def_TightQLearning_qStar
import Definitions.Def_TightQLearning_RateBand
import Definitions.Def_TightQLearning_IsGenerativeModel
import Definitions.Def_TightQLearning_windowMax

open QLearning.Convergence MeasureTheory

namespace TightQLearning

/-- Lemma 2 (Li, Cai, Chen, Wei & Chi, arXiv:2102.06548v4, p.14): if `c₁c₂ ≤ c₄/8`, then with
probability at least `1 − δ`, `Δ_t ≥ −30 √((log⁴T)(log(|S||A|T/δ))/(γ²(1−γ)⁴T) · (1 + max_{t/2≤i<t} ‖Δ_i‖_∞)) 1`
holds simultaneously for all `t ≥ T/(c₂ log T)`.

**Formalization Note.** The page's standing hypotheses are written out: `γ ∈ (0,1)`, `δ ∈ (0,1)`,
(16a), the box for `Q₀`, and (63) in its `≥` form with a constant `c₃` chosen after `c₁, c₂`. `c₄`
is the paper's constant of (37). "All `t`" means `t ≤ T`, since the rates are constrained only up
to `T`. `2 ≤ t` makes the window nonempty; for `t = 1` the page's maximum is undefined. `2 ≤ T`
excludes the undefined `log³T = 0`. The quantifier over `t` sits inside the event. -/
theorem lemma_2 :
    ∃ c₄ : ℝ, 0 < c₄ ∧ ∀ c₁ c₂ : ℝ, 0 < c₂ → c₂ ≤ c₁ → c₁ * c₂ ≤ c₄ / 8 →
      ∃ c₃ : ℝ, 0 < c₃ ∧
        ∀ (X A : Type) [Fintype X] [DecidableEq X] [Nonempty X]
          [Fintype A] [DecidableEq A] [Nonempty A]
          (M : FiniteMDP X A) (_hr : ∀ s a, 0 ≤ M.R s a ∧ M.R s a ≤ 1)
          (γ δ : ℝ) (_hγ : 0 < γ ∧ γ < 1) (_hδ : 0 < δ ∧ δ < 1)
          (T : ℕ) (_hT : 2 ≤ T) (η : ℕ → ℝ) (_hη : RateBand c₁ c₂ γ T η)
          (_h63 : (T : ℝ) ≥ c₃ * (Real.log T ^ 4 *
            Real.log ((Fintype.card X : ℝ) * (Fintype.card A : ℝ) * (T : ℝ) / δ)) / (1 - γ) ^ 3)
          (Q0 : X → A → ℝ) (_hQ0 : ∀ s a, 0 ≤ Q0 s a ∧ Q0 s a ≤ 1 / (1 - γ))
          {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
          (sample : ℕ → X → A → Ω → X) (_hs : IsGenerativeModel M T μ sample),
          ENNReal.ofReal (1 - δ) ≤ μ {ω | ∀ (t : ℕ) (ht : 2 ≤ t),
            (T : ℝ) / (c₂ * Real.log T) ≤ t → t ≤ T → ∀ s a,
              syncQ M γ η Q0 (fun t' s' a' => sample t' s' a' ω) t s a - qStar M γ s a ≥
                -30 * Real.sqrt ((Real.log T ^ 4 *
                  Real.log ((Fintype.card X : ℝ) * (Fintype.card A : ℝ) * (T : ℝ) / δ)) /
                  (γ ^ 2 * (1 - γ) ^ 4 * (T : ℝ)) *
                (1 + windowMax t ht (fun i =>
                  ‖syncQ M γ η Q0 (fun t' s' a' => sample t' s' a' ω) i - qStar M γ‖)))} := by sorry

end TightQLearning
