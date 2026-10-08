-- Prove2me | Theorems.Thm_SchalAvg_AvgOpt_theorem_3_8
-- name    : SchalAvg.AvgOpt.theorem_3_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:51:29.738086+00:00
-- url     : https://prove2.me/theorems/7f30d7ef-caa2-4069-aeeb-2e66a42d230b
-- title:
--   Theorem 3.8 — under (W) or (S) and (B) an average-optimal, limit discount optimal stationary policy exists, and g = lim (1 − β)m_β = lim (1 − β)v_β
-- statement:
--   Consider Schäl's decision model $(S, A, A(\cdot), q, c)$: standard Borel state and action spaces, nonempty action sets $A(x)$ with measurable graph, a transition law $q$, and a one-step cost $c \ge 0$ (possibly $+\infty$). Assume the General Assumption $g = \inf_x \inf_{\delta} \Phi(\delta, x) < \infty$ and Condition (B), $\sup_{0<\beta<1} w_\beta(x) < \infty$ for every $x$. Assume Condition (W) or Condition (S). Then:
--
--   1. **Under (W).** There is a stationary policy $f_1 \in \mathbb F$ that is **average optimal**: $\Phi(f_1, x) = g$ for all $x \in S$. Moreover, for *any* sequence of discount factors $\beta(k) \in (0, 1)$ with $\beta(k) \to 1$ and any choice of $\beta(k)$-discount optimal stationary policies $f_{\beta(k)}$, there is an average-optimal $f_1 \in \mathbb F$ that is **limit discount optimal** in the sense of Proposition 3.5(ii): for every $x$ there are $\beta_m \to 1$ from $\{\beta(k)\}$ and $x_m \to x$ with $f_1(x) = \lim_m f_{\beta_m}(x_m)$.
--   2. **Under (S).** The same holds with limit discount optimality in the sense of (3.7): for every $x$ there are $\beta_m \to 1$ from $\{\beta(k)\}$ with $f_1(x) = \lim_m f_{\beta_m}(x)$.
--   3. Under (W) or (S),
--   $$g = \lim_{\beta \to 1} (1 - \beta) m_\beta = \lim_{\beta \to 1} (1 - \beta) v_\beta(x) \qquad \text{for every } x \in S.$$
--
--   The theorem derives the existence of an average-optimal stationary policy, and the vanishing-discount characterization of the optimal average cost, from compactness–continuity conditions on the model and pointwise boundedness of the relative discounted values alone, without assuming an average cost optimality equation or inequality.
--
--   **Formalization Note.** The paper's "There $\{\beta(k)\}$ can be any sequence of discount factors converging to one" is pinned as: for every such sequence and every choice of discount-optimal stationary $f_{\beta(k)}$ there is an average-optimal, limit discount optimal $f_1$. The unconditional existence of an average-optimal $f_1$ is stated separately, so that it does not depend on the existence of the $f_{\beta(k)}$ (Proposition 2.1). When (W) and (S) both hold, the two limit properties are claimed for possibly different $f_1$, as in the paper. "$\beta_m \to 1$, $\{\beta_m\} \subset \{\beta(k)\}$" is $\beta_m = \beta(k_m)$ with $k_m \to \infty$. $\lim_{\beta \to 1}(1-\beta)v_\beta$ is pointwise in $x$, with $\beta \uparrow 1$ (`𝓝[<] 1`). The topology on $S$ is an instance; Condition (W) ties it to the σ-algebra and makes it locally compact, second countable and Hausdorff, while the (S) branch uses no topology on $S$. The General Assumption is the paper's standing assumption (p. 164). Values are in $[0, \infty]$; all infima are over admissible policies.
-- source:
--   Schäl, Average Optimality in Dynamic Programming with General State Space, Math. Oper. Res. 18(1) (1993), p. 168, Theorem 3.8

import Mathlib
import Definitions.Def_FeinbergLiang_ACOE_MDP
import Definitions.Def_SchalAvg_AvgOpt_Model

open scoped ENNReal NNReal Topology
open MeasureTheory ProbabilityTheory Filter FeinbergLiang.ACOE

namespace SchalAvg.AvgOpt

theorem theorem_3_8 {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S] [TopologicalSpace S]
    [TopologicalSpace A] [TopologicalSpace.MetrizableSpace A] [SecondCountableTopology A]
    [MeasurableSpace A] [BorelSpace A] [StandardBorelSpace A]
    (M : Model S A) (hGA : GeneralAssumption M) (hB : CondB M) :
    -- Condition (W): an average-optimal f₁, and limit discount optimality in the sense of 3.5(ii)
    (CondW M →
      (∃ f₁ : S → A, ∃ hf₁ : IsStationary M f₁, ∀ x, Phi M (statPolicy hf₁) x = gStar M) ∧
      ∀ β : ℕ → ℝ, (∀ k, β k ∈ Set.Ioo (0 : ℝ) 1) → Tendsto β atTop (𝓝 1) →
      ∀ fβ : ℕ → S → A, (∀ k, IsDiscOptimal M (β k) (fβ k)) →
        ∃ f₁ : S → A, ∃ hf₁ : IsStationary M f₁,
          (∀ x, Phi M (statPolicy hf₁) x = gStar M) ∧
          ∀ x, ∃ (km : ℕ → ℕ) (xm : ℕ → S), Tendsto km atTop atTop ∧
            Tendsto xm atTop (𝓝 x) ∧ Tendsto (fun m => fβ (km m) (xm m)) atTop (𝓝 (f₁ x))) ∧
    -- Condition (S): an average-optimal f₁, and limit discount optimality in the sense of (3.7)
    (CondS M →
      (∃ f₁ : S → A, ∃ hf₁ : IsStationary M f₁, ∀ x, Phi M (statPolicy hf₁) x = gStar M) ∧
      ∀ β : ℕ → ℝ, (∀ k, β k ∈ Set.Ioo (0 : ℝ) 1) → Tendsto β atTop (𝓝 1) →
      ∀ fβ : ℕ → S → A, (∀ k, IsDiscOptimal M (β k) (fβ k)) →
        ∃ f₁ : S → A, ∃ hf₁ : IsStationary M f₁,
          (∀ x, Phi M (statPolicy hf₁) x = gStar M) ∧
          ∀ x, ∃ km : ℕ → ℕ, Tendsto km atTop atTop ∧
            Tendsto (fun m => fβ (km m) x) atTop (𝓝 (f₁ x))) ∧
    -- g = lim_{β → 1} (1 − β) m_β = lim_{β → 1} (1 − β) v_β
    (CondW M ∨ CondS M →
      Tendsto (fun β : ℝ => ENNReal.ofReal (1 - β) * mβ M β) (𝓝[<] 1) (𝓝 (gStar M)) ∧
      ∀ x, Tendsto (fun β : ℝ => ENNReal.ofReal (1 - β) * vβ M β x) (𝓝[<] 1)
        (𝓝 (gStar M))) := by sorry

end SchalAvg.AvgOpt
