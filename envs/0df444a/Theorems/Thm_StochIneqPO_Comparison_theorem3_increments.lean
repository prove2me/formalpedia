-- Prove2me | Theorems.Thm_StochIneqPO_Comparison_theorem3_increments
-- name    : StochIneqPO.Comparison.theorem3_increments
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:17:52.58498+00:00
-- url     : https://prove2.me/theorems/97b0e125-a4a0-421e-9fdf-4ac9ac4c29c3
-- title:
--   Theorem 3 — comparison of increments in a partially ordered Polish vector space
-- statement:
--   Let $E$ be a partially ordered Polish space which also carries a compatible vector space structure over $\mathbb R$: addition and scalar multiplication are continuous, and for every increasing (measurable) set $A \subseteq E$ and every $x \in E$ the translate $A + x = \{y + x : y \in A\}$ is again increasing. Let $P_1, Q_1$ be probability measures on $E$ with $P_1 \prec Q_1$, and for $n = 2, 3, \dots$ let $p_n, q_n$ be stochastic kernels from $E^{n-1}$ to $E$. Assume
--   $$p_{n+1}(s_1, \dots, s_n;\ s_n + A) \le q_{n+1}(t_1, \dots, t_n;\ t_n + A) \tag{7}$$
--   for all $n \ge 1$, all $s^n, t^n \in E^n$ with $s_1 \le t_1$ and $s_{i+1} - s_i \le t_{i+1} - t_i$ for $i = 1, \dots, n-1$, and all increasing sets $A$. Then there are processes $(S_n)_{n \ge 1}$ and $(T_n)_{n \ge 1}$ on a common probability space such that $S_1 \sim P_1$, $T_1 \sim Q_1$, the conditional distribution of $S_{n+1}$ given $S_1, \dots, S_n$ is $p_{n+1}(S_1, \dots, S_n; \cdot)$, that of $T_{n+1}$ given $T_1, \dots, T_n$ is $q_{n+1}(T_1, \dots, T_n; \cdot)$, and
--   $$P\big(S_{n+1} - S_n \le T_{n+1} - T_n,\ n = 1, 2, \dots\big) = 1, \qquad P(S_1 \le T_1) = 1.$$
--
--   Hypothesis (7) compares the kernels only through the increment each one produces, and the conclusion orders the increments of the two processes rather than their values. It is obtained from Theorem 2 by a change of variables and is related to Example 7.2 of O'Brien (1975).
--
--   **Formalization Note** The paper writes the conditional increment law of $T$ as $q_{n+1}(T_1, \dots, T_n; A + S_n)$; this is a misprint for $A + T_n$ (the law of $T$ cannot depend on $S$, and the proof sets $T_n = Y_1 + \dots + Y_n$ with $Y$ driven by $q$ alone). The Lean states the corrected form. "$P(S_{n+1} - S_n \in A \mid S^n) = p_{n+1}(S^n; A + S_n)$ for all $A$" says that $p_{n+1}(S^n, \cdot)$ is the conditional law of $S_{n+1}$; together with $S_1 \sim P_1$ this is encoded, as in Theorem 2, by the joint law of $(S_n)$ being `Kernel.trajMeasure P₁ p` (and that of $(T_n)$ being `trajMeasure Q₁ q`). Indices are 0-based: the paper's $S_i$ is `S (i - 1)`, and the paper's $p_{n+1}$ ($n \ge 1$), acting on $(s_1, \dots, s_n)$, is `p (n - 1)` acting on coordinates `0, …, n - 1`; in (7) the histories are given as sequences `s t : ℕ → E` restricted to those coordinates, which ranges over all of $E^n$. The vector structure is `[AddCommGroup E] [Module ℝ E] [ContinuousAdd E] [ContinuousSMul ℝ E]`, and translation invariance of increasing sets is the hypothesis `hcompat`; the standing assumption of Sec. 1 (partially ordered Polish space, closed order, Borel σ-algebra) is carried as instances.
-- source:
--   Kamae, Krengel, O'Brien, Stochastic Inequalities on Partially Ordered Spaces, Ann. Probab. 5 (1977), Theorem 3, eq. (7), p. 904 (PDF p. 6)

import Mathlib
import Definitions.Def_StochIneqPO_Comparison_StochLE

namespace StochIneqPO.Comparison

open MeasureTheory ProbabilityTheory Finset

theorem theorem3_increments {E : Type*} [TopologicalSpace E] [PolishSpace E] [MeasurableSpace E]
    [BorelSpace E] [PartialOrder E] [OrderClosedTopology E]
    [AddCommGroup E] [Module ℝ E] [ContinuousAdd E] [ContinuousSMul ℝ E]
    (hcompat : ∀ (A : Set E) (x : E), MeasurableSet A → IsUpperSet A →
      IsUpperSet ((fun y => y + x) '' A))
    (P₁ Q₁ : Measure E) [IsProbabilityMeasure P₁] [IsProbabilityMeasure Q₁]
    (p q : (n : ℕ) → Kernel (Π _ : Iic n, E) E)
    [∀ n, IsMarkovKernel (p n)] [∀ n, IsMarkovKernel (q n)]
    (hPQ : StochLE P₁ Q₁)
    (h7 : ∀ (n : ℕ) (s t : ℕ → E), s 0 ≤ t 0 →
      (∀ i < n, s (i + 1) - s i ≤ t (i + 1) - t i) →
      ∀ A : Set E, MeasurableSet A → IsUpperSet A →
        p n (fun j => s j) ((fun y => s n + y) '' A) ≤
          q n (fun j => t j) ((fun y => t n + y) '' A)) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω), IsProbabilityMeasure μ ∧
      ∃ (S T : ℕ → Ω → E), (∀ n, Measurable (S n)) ∧ (∀ n, Measurable (T n)) ∧
        μ.map (fun ω n => S n ω) = Kernel.trajMeasure (X := fun _ => E) P₁ p ∧
        μ.map (fun ω n => T n ω) = Kernel.trajMeasure (X := fun _ => E) Q₁ q ∧
        (∀ᵐ ω ∂μ, ∀ n, S (n + 1) ω - S n ω ≤ T (n + 1) ω - T n ω) ∧
        (∀ᵐ ω ∂μ, S 0 ω ≤ T 0 ω) := by sorry

end StochIneqPO.Comparison
