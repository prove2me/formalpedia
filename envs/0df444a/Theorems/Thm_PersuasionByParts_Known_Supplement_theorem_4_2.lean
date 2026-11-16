-- Prove2me | Theorems.Thm_PersuasionByParts_Known_Supplement_theorem_4_2
-- name    : PersuasionByParts.Known.Supplement.theorem_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:50:32.612192+00:00
-- url     : https://prove2.me/theorems/d06a9056-843c-4f7e-a250-f8d1fb9143a2
-- title:
--   Theorem 4.2 (i)–(ii) — No universal quadratic bound for a single product experiment
-- statement:
--   For a product prior and a cutoff $t$, $V_{\rm joint}(t)$ is the largest achievable probability that the posterior mean of the sum is at least $t$ under a joint experiment, and $V_\Pi(t)$ is the probability that the sum of the coordinate posterior means is at least $t$ under a given product experiment $\Pi$.
--
--   For every integer $n\ge2$:
--
--   1. There are $n+1$ independent nonnegative coordinates $X_0,X_1,\dots,X_n$, each supported on two points, and two cutoffs $t_{\rm lo}<t_{\rm hi}$ with $V_{\rm joint}(t_{\rm lo})>0$ and $V_{\rm joint}(t_{\rm hi})>0$, such that every product experiment $\Pi$ satisfies
--   $$\min_{t\in\{t_{\rm lo},t_{\rm hi}\}}\frac{V_\Pi(t)}{V_{\rm joint}(t)^2}\ <\ \frac{\ln(n+1)}{n}.$$
--   2. For every $\gamma\in(0,1/2]$ there is a constant $c_\gamma>0$, depending only on $\gamma$, such that for every $n\ge2$ there are $n+1$ independent nonnegative coordinates $X_0,\dots,X_n$, each supported on two points, and two cutoffs $t_{\rm lo}<t_{\rm hi}$ with $V_{\rm joint}(t_{\rm lo})=1$ and $Q:=V_{\rm joint}(t_{\rm hi})\in(0,2^{-n})$, such that every product experiment $\Pi$ with $V_\Pi(t_{\rm lo})\ge\gamma$ satisfies
--   $$V_\Pi(t_{\rm hi})\ \le\ 5\,Q^2\exp\!\Big(-c_\gamma\,\frac{\ln(1/Q)}{\ln\ln(1/Q)}\Big).$$
--
--   Part 1 shows that no single product experiment achieves $V_\Pi(t)\ge c\,V_{\rm joint}(t)^2$ at all cutoffs with $c$ independent of $n$; part 2 shows that the sub-polynomial factor in the universal guarantee (Theorem 3.1) is tight up to the constant in the exponent.
--
--   Differences from the source:
--   - encoding: n + 1 independent coordinates X_0, X_1, …, X_n → P : Prior (n + 1) (coordinates indexed by Fin (n + 1), product law, finite means); reason: independence is the product form of the published prior; finite means hold for two-point laws
--   - encoding: each nonnegative and supported on two points → for every coordinate i there are reals 0 ≤ a < b with P_i({a, b}) = 1, P_i({a}) > 0 and P_i({b}) > 0; reason: this says the support is exactly a two-point subset of [0, ∞)
--   - encoding: (i) the ratio V_Π(t)/V_joint(t)² for t ∈ {t_lo, t_hi} → the conclusion also states 0 < V_joint(t_lo) and 0 < V_joint(t_hi), and the ratio uses real division; reason: the ratio is defined only when V_joint(t) > 0; stating positivity rules out Lean's x/0 = 0 making the inequality hold trivially
--   - encoding: (ii) c_γ > 0 depends only on γ → ∃ cγ > 0 quantified after γ and before n and the instance; reason: the constant is uniform over n, the coordinates, the cutoffs and the experiment
--   - encoding: Q ∈ (0, 2^{−n}), ln, ln ln → 0 < Q ∧ Q < (1/2)^n, Real.log, Real.log ∘ Real.log; reason: the same numbers; Q < 1/4 makes ln ln(1/Q) positive
-- source:
--   Shuyuan Jia, Kangning Wang, Renzhe Xu, Persuasion by Parts, STOC 2027 submission #314 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/314.pdf, printed p. 17 / PDF p. 18, Theorem 4.2 (No universal quadratic bound), parts (i) and (ii)

import Mathlib
import Definitions.Def_PersuasionByParts_Known_Model

open MeasureTheory ProbabilityTheory Set
noncomputable section

namespace PersuasionByParts.Known.Supplement

/-- Theorem 4.2, printed p. 17 / PDF p. 18, both parts, for `n + 1` coordinates
`X_0, …, X_n` (`Fin (n + 1)`), each nonnegative and supported on exactly two points
(both atoms of positive mass); independence is the product form of `Prior`.
(i) Both joint cutoff values are positive, so the ratios are genuine, and every product
experiment has `min_t V_E(t) / V_joint(t)² < ln(n+1)/n` over `t ∈ {t_lo, t_hi}`.
(ii) `c_γ > 0` depends only on `γ` (chosen before `n`); `V_joint(t_lo) = 1`,
`Q = V_joint(t_hi) ∈ (0, 2^(-n))`, and every product experiment with `V_E(t_lo) ≥ γ` has
`V_E(t_hi) ≤ 5 Q² exp(-c_γ ln(1/Q) / ln ln(1/Q))`. -/
theorem theorem_4_2 :
    (∀ n : ℕ, 2 ≤ n →
      ∃ (P : Prior (n + 1)) (tlo thi : ℝ),
        (∀ i, ∃ a b : ℝ, 0 ≤ a ∧ a < b ∧ P.marginal i {a, b} = 1 ∧
          0 < P.marginal i {a} ∧ 0 < P.marginal i {b}) ∧
        tlo < thi ∧ 0 < jointCutoff P tlo ∧ 0 < jointCutoff P thi ∧
        ∀ E : ProductExperiment (n + 1),
          min (productPayoff P E (cutoff tlo) / jointCutoff P tlo ^ 2)
              (productPayoff P E (cutoff thi) / jointCutoff P thi ^ 2) <
            Real.log ((n : ℝ) + 1) / n) ∧
    (∀ γ : ℝ, γ ∈ Ioc (0 : ℝ) (1 / 2) →
      ∃ cγ : ℝ, 0 < cγ ∧
      ∀ n : ℕ, 2 ≤ n →
        ∃ (P : Prior (n + 1)) (tlo thi : ℝ),
          (∀ i, ∃ a b : ℝ, 0 ≤ a ∧ a < b ∧ P.marginal i {a, b} = 1 ∧
            0 < P.marginal i {a} ∧ 0 < P.marginal i {b}) ∧
          tlo < thi ∧ jointCutoff P tlo = 1 ∧
          0 < jointCutoff P thi ∧ jointCutoff P thi < (1 / 2 : ℝ) ^ n ∧
          ∀ E : ProductExperiment (n + 1), productPayoff P E (cutoff tlo) ≥ γ →
            productPayoff P E (cutoff thi) ≤
              5 * jointCutoff P thi ^ 2 *
                Real.exp (-cγ * (Real.log (1 / jointCutoff P thi) /
                  Real.log (Real.log (1 / jointCutoff P thi))))) := by sorry

end PersuasionByParts.Known.Supplement
