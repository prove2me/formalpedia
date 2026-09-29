-- Prove2me | Theorems.Thm_Soar_greedy_fails
-- name    : Soar.greedy_fails
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-23T02:42:42.463519+00:00
-- url     : https://prove2.me/theorems/dcbdacf7-f26d-4efa-9c93-50a5341dbcb5
-- title:
--   Failure of Greedy (Proposition 1)
-- statement:
--   Let the supply distribution $Q$ on $\mathbb R$ be supported on the atoms $\{0, 1\}$ with $Q(\{1\}) = \rho$ and $Q(\{0\}) = 1 - \rho$ for a fixed $\rho \in (0, 1)$, and let the demand distribution $P$ be a continuous distribution on $[0, 1]$ with a density $f_P$ bounded below and above, $\gamma^{-1} \le f_P \le \gamma$ on $[0, 1]$ for some $\gamma \ge 1$, with cumulative distribution function $F_P$ satisfying $F_P(1/2) \ne 1 - \rho$. Fix $p \ge 1$ and the quality function $\varphi(x, y) = -|x - y|^p$. Then there are a constant $c = c(\rho, F_P, p) > 0$ and an $n_0 \in \mathbb N$ such that for every horizon $n \ge n_0$ and every Greedy policy — every dynamic matching policy, on any seed space, that matches each arriving demand unit to an available supply unit maximizing $\varphi(X_t, \cdot)$, with any tie-breaking rule —
--   $$\mathrm{Reg}_n(\mathrm{Greedy}) \ge c .$$
--
--   **Role.** This is Proposition 1, the paper's evidence that myopic matching is insufficient: Greedy is near-optimal for identical uniform distributions (Kanoria 2022; Akbarpour et al. 2021) but has non-vanishing regret as soon as the supply distribution differs from the demand distribution in this simple way. It motivates the forward-looking SOAR policy, whose regret vanishes for every bounded instance by Corollary 1.
--
--   **Formalization Note** The instance is stated on the real line with $\mathcal X = \mathcal Y = \mathbb R$: $Q = \rho\,\delta_1 + (1 - \rho)\,\delta_0$ and $P$ is Lebesgue measure with a density that vanishes outside $[0,1]$ and lies in $[\gamma^{-1}, \gamma]$ there; $F_P(1/2) = P((-\infty, 1/2])$. Both $P$ and $Q$ are required to be probability measures. Under a continuous $P$ the Greedy decision has a tie only on the null event $X_t = 1/2$, so the conclusion is stated for every Greedy policy with the constant chosen before the policy, as in the paper, where $c$ depends only on $(\rho, F_P, p)$. The quantifier "for all $n \ge n_0$" is the paper's.
-- source:
--   Y. Chen, Y. Kanoria, A. Kumar, W. Zhang, Feature-Based Dynamic Matching, SSRN working paper 4451799 (version of 27 May 2025; extended abstract in Proc. 24th ACM Conference on Economics and Computation, EC'23), https://ssrn.com/abstract=4451799, Section 3.1, Proposition 1, and Appendix B.1

import Mathlib
import Definitions.Def_SoarPolicies
import Definitions.Def_SoarEuclidean

open MeasureTheory

universe u

namespace Soar

theorem greedy_fails (ρ γ p : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hp : 1 ≤ p)
    (P Q : Measure ℝ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hQ : Q = ENNReal.ofReal ρ • Measure.dirac (1 : ℝ) +
      ENNReal.ofReal (1 - ρ) • Measure.dirac (0 : ℝ))
    (hP : SoarHasDensityOn (Set.Icc (0 : ℝ) 1) P γ)
    (hF : (P (Set.Iic (1 / 2 : ℝ))).toReal ≠ 1 - ρ) :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (π : SoarDynamicPolicy ℝ ℝ Ω n), SoarIsGreedy (SoarAbsQuality p) π →
          c ≤ SoarPolicyRegret P Q μ (SoarAbsQuality p) π := by
  sorry

end Soar
