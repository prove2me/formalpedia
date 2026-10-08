-- Prove2me | Theorems.Thm_SchalAvg_AvgOpt_prop_3_5_S
-- name    : SchalAvg.AvgOpt.prop_3_5_S
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:51:24.996993+00:00
-- url     : https://prove2.me/theorems/748b8de6-16fa-42d4-a6dc-8ccaf43bea66
-- title:
--   §3, p. 168, (3.7) — Proposition 3.5 under (S): the optimality inequality for liminf_k w_{β(k)} and f₁(x) = lim f_{β_m}(x)
-- statement:
--   In Schäl's decision model $(S, A, A(\cdot), q, c)$ assume the General Assumption, Condition (S) and Condition (B). Let $\beta(k) \in (0, 1)$ be discount factors with $\beta(k) \to 1$ and $(1 - \beta(k)) m_{\beta(k)} \to \underline g$ (3.1), and for each $k$ let $f_{\beta(k)}$ be a $\beta(k)$-discount optimal stationary policy. With the discrete metric the lower limit of §3 becomes
--   $$\underline w(x) = \liminf_{k \to \infty} w_{\beta(k)}(x).$$
--   Then there is $f_1 \in \mathbb F$ such that
--
--   1. $$\underline w(x) + \underline g \ \ge\ c(x, f_1(x)) + \int \underline w \, dq(x, f_1(x)), \qquad x \in S;$$
--   2. (3.7) for every $x \in S$ there is a sequence $\beta_m \to 1$ taken from $\{\beta(k)\}$ such that $f_1(x) = \lim_{m \to \infty} f_{\beta_m}(x)$.
--
--   Under (S) the action limit is taken at the state $x$ itself, in contrast to Proposition 3.5(ii) under (W).
--
--   **Formalization Note.** The paper states this as "a similar analysis can be carried through under condition (S)", obtained by "formally choosing $\rho$ as the metric of the discrete topology", and gives (3.7) "instead of (ii) of 3.5"; part 1 is Proposition 3.5(i) for the discrete-metric $\underline w$. No topology on $S$ is used. "$\beta_m \to 1$, $\{\beta_m\} \subset \{\beta(k)\}$" is encoded as $\beta_m = \beta(k_m)$ with $k_m \to \infty$.
-- source:
--   Schäl, Average Optimality in Dynamic Programming with General State Space, Math. Oper. Res. 18(1) (1993), §3, p. 168, (3.7) (Proposition 3.5 under Condition (S))

import Mathlib
import Definitions.Def_FeinbergLiang_ACOE_MDP
import Definitions.Def_SchalAvg_AvgOpt_Model

open scoped ENNReal NNReal Topology
open MeasureTheory ProbabilityTheory Filter FeinbergLiang.ACOE

namespace SchalAvg.AvgOpt

theorem prop_3_5_S {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S]
    [TopologicalSpace A] [TopologicalSpace.MetrizableSpace A] [SecondCountableTopology A]
    [MeasurableSpace A] [BorelSpace A] [StandardBorelSpace A]
    (M : Model S A) (hGA : GeneralAssumption M) (hS : CondS M) (hB : CondB M)
    (β : ℕ → ℝ) (hβ : ∀ k, β k ∈ Set.Ioo (0 : ℝ) 1) (hβ1 : Tendsto β atTop (𝓝 1))
    (h31 : Tendsto (fun k => ENNReal.ofReal (1 - β k) * mβ M (β k)) atTop (𝓝 (gLower M)))
    (fβ : ℕ → S → A) (hfβ : ∀ k, IsDiscOptimal M (β k) (fβ k)) :
    ∃ f₁ : S → A, IsStationary M f₁ ∧
      (∀ x, M.toMDP.cost x (f₁ x) + ∫⁻ y, wLowDisc M β y ∂(M.toMDP.q (x, f₁ x)) ≤
        wLowDisc M β x + gLower M) ∧
      ∀ x, ∃ km : ℕ → ℕ, Tendsto km atTop atTop ∧
        Tendsto (fun m => fβ (km m) x) atTop (𝓝 (f₁ x)) := by sorry

end SchalAvg.AvgOpt
