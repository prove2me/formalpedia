-- Prove2me | Theorems.Thm_SchalAvg_AvgOpt_lemma_3_4
-- name    : SchalAvg.AvgOpt.lemma_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:51:41.039721+00:00
-- url     : https://prove2.me/theorems/2ba328f7-0f9c-47fd-adde-1bec40af4d50
-- title:
--   Lemma 3.4 — under (W) and (B), measurable k_n → ∞ and y_n → x with w(k_n(x), y_n(x)) → w̲(x); w̲ is measurable and finite
-- statement:
--   In Schäl's decision model $(S, A, A(\cdot), q, c)$ let $\rho$ be a metric on $S$ defining its topology, and assume the General Assumption, Condition (W) and Condition (B). Let $\beta(k)$ be discount factors in $(0, 1)$, $w(k, x) = w_{\beta(k)}(x)$ and $\underline w(x) = \liminf_{k \to \infty,\ y \to x} w(k, y)$. Then there are sequences $(k_n)$ of measurable integer-valued mappings and $(y_n)$ of measurable $S$-valued mappings on $S$ such that, for every $x \in S$,
--
--   1. $k_n(x) \to \infty$ and $y_n(x) \to x$ as $n \to \infty$;
--   2. $$w(k_n(x), y_n(x)) \to \underline w(x) \qquad (n \to \infty);$$
--
--   and $\underline w$ is measurable with values in $[0, \infty)$.
--
--   The lemma realizes the generalized lower limit $\underline w$ along measurably chosen sequences, so that the relative optimality equation (2.2), evaluated at $(\beta(k_n(x)), y_n(x))$, can be passed to the limit pointwise in $x$.
--
--   **Formalization Note.** The integer-valued mappings are $\mathbb N$-valued. The General Assumption is the paper's standing assumption. The paper's fixed sequence with (3.1) is replaced by an arbitrary sequence in $(0, 1)$, which the statement does not need otherwise; a harmless generalization.
-- source:
--   Schäl, Average Optimality in Dynamic Programming with General State Space, Math. Oper. Res. 18(1) (1993), pp. 166–167, Lemma 3.4

import Mathlib
import Definitions.Def_FeinbergLiang_ACOE_MDP
import Definitions.Def_SchalAvg_AvgOpt_Model

open scoped ENNReal NNReal Topology
open MeasureTheory ProbabilityTheory Filter FeinbergLiang.ACOE

namespace SchalAvg.AvgOpt

theorem lemma_3_4 {S A : Type*} [MetricSpace S] [MeasurableSpace S] [StandardBorelSpace S]
    [TopologicalSpace A] [TopologicalSpace.MetrizableSpace A] [SecondCountableTopology A]
    [MeasurableSpace A] [BorelSpace A] [StandardBorelSpace A]
    (M : Model S A) (hGA : GeneralAssumption M) (hW : CondW M) (hB : CondB M)
    (β : ℕ → ℝ) (hβ : ∀ k, β k ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ (kn : ℕ → S → ℕ) (yn : ℕ → S → S),
      (∀ n, Measurable (kn n)) ∧ (∀ n, Measurable (yn n)) ∧
      (∀ x, Tendsto (fun n => kn n x) atTop atTop) ∧
      (∀ x, Tendsto (fun n => yn n x) atTop (𝓝 x)) ∧
      (∀ x, Tendsto (fun n => wβ M (β (kn n x)) (yn n x)) atTop (𝓝 (wLow M β x))) ∧
      Measurable (wLow M β) ∧ ∀ x, wLow M β x ≠ ⊤ := by sorry

end SchalAvg.AvgOpt
