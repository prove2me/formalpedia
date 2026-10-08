-- Prove2me | Theorems.Thm_SchalAvg_AvgOpt_prop_3_5
-- name    : SchalAvg.AvgOpt.prop_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:51:06.877543+00:00
-- url     : https://prove2.me/theorems/c3c665bf-4d0a-46f2-861a-33f3dae66ebc
-- title:
--   Proposition 3.5 — under (W) and (B), w̲ and some f₁ ∈ 𝔽 satisfy the optimality inequality with g̲, and f₁ is a limit of f_{β_m}(x_m)
-- statement:
--   In Schäl's decision model $(S, A, A(\cdot), q, c)$ let $\rho$ be a metric on $S$ defining its topology, and assume the General Assumption, Condition (W) and Condition (B). Let $\beta(k) \in (0, 1)$ be discount factors with $\beta(k) \to 1$ and
--   $$(1 - \beta(k)) m_{\beta(k)} \to \underline g \tag{3.1}$$
--   and, for each $k$, let $f_{\beta(k)}$ be a $\beta(k)$-discount optimal stationary policy (Proposition 2.1). Let $\underline w(x) = \liminf_{k \to \infty,\ y \to x} w_{\beta(k)}(y)$. Then there is $f_1 \in \mathbb F$ such that
--
--   1. $$\underline w(x) + \underline g \ \ge\ c(x, f_1(x)) + \int \underline w \, dq(x, f_1(x)), \qquad x \in S;$$
--   2. for every $x \in S$ there are discount factors $\beta_m \to 1$ taken from $\{\beta(k)\}$ and states $x_m \to x$ such that $f_1(x) = \lim_{m \to \infty} f_{\beta_m}(x_m)$.
--
--   Part 1 is exactly the hypothesis of Proposition 1.3; part 2 says that $f_1(x)$ is a limit of discount-optimal actions, possibly at nearby states rather than at $x$ itself.
--
--   **Formalization Note.** "$\beta_m \to 1$, $\{\beta_m\} \subset \{\beta(k)\}$" is encoded as $\beta_m = \beta(k_m)$ with indices $k_m \to \infty$ (not necessarily increasing), and $f_{\beta_m}$ as $f_{\beta(k_m)}$; since every $\beta(k) < 1$ and $\beta(k) \to 1$, $\beta(k_m) \to 1$ is equivalent to $k_m \to \infty$. The family $f_{\beta(k)}$ is arbitrary (any discount-optimal choice per index). The constant in part 1 is $\underline g$ (underlined in the paper). The General Assumption is the paper's standing assumption.
-- source:
--   Schäl, Average Optimality in Dynamic Programming with General State Space, Math. Oper. Res. 18(1) (1993), p. 167, Proposition 3.5

import Mathlib
import Definitions.Def_FeinbergLiang_ACOE_MDP
import Definitions.Def_SchalAvg_AvgOpt_Model

open scoped ENNReal NNReal Topology
open MeasureTheory ProbabilityTheory Filter FeinbergLiang.ACOE

namespace SchalAvg.AvgOpt

theorem prop_3_5 {S A : Type*} [MetricSpace S] [MeasurableSpace S] [StandardBorelSpace S]
    [TopologicalSpace A] [TopologicalSpace.MetrizableSpace A] [SecondCountableTopology A]
    [MeasurableSpace A] [BorelSpace A] [StandardBorelSpace A]
    (M : Model S A) (hGA : GeneralAssumption M) (hW : CondW M) (hB : CondB M)
    (β : ℕ → ℝ) (hβ : ∀ k, β k ∈ Set.Ioo (0 : ℝ) 1) (hβ1 : Tendsto β atTop (𝓝 1))
    (h31 : Tendsto (fun k => ENNReal.ofReal (1 - β k) * mβ M (β k)) atTop (𝓝 (gLower M)))
    (fβ : ℕ → S → A) (hfβ : ∀ k, IsDiscOptimal M (β k) (fβ k)) :
    ∃ f₁ : S → A, IsStationary M f₁ ∧
      (∀ x, M.toMDP.cost x (f₁ x) + ∫⁻ y, wLow M β y ∂(M.toMDP.q (x, f₁ x)) ≤
        wLow M β x + gLower M) ∧
      ∀ x, ∃ (km : ℕ → ℕ) (xm : ℕ → S), Tendsto km atTop atTop ∧ Tendsto xm atTop (𝓝 x) ∧
        Tendsto (fun m => fβ (km m) (xm m)) atTop (𝓝 (f₁ x)) := by sorry

end SchalAvg.AvgOpt
