-- Prove2me | Theorems.Thm_RossQC_Sufficient_theorem_3_7
-- name    : RossQC.Sufficient.theorem_3_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:40:52.488997+00:00
-- url     : https://prove2.me/theorems/5fb6be5f-b092-4737-a819-92bb14943415
-- title:
--   Theorem 3.7 — sufficient conditions for three-region and no-inspection policies
-- statement:
--   Consider the two-state model with $0<\beta<1$, $0\le\pi\le1$, and $0<C<I<R$. Write $V_\beta$ for the discounted value of equation (3).
--
--   1. If
--      $$
--      \frac{(1-\beta)(R+\beta V_\beta(\pi))}{C}\le\frac{R-I}{\beta(V_\beta(1)-V_\beta(\pi))},
--      $$
--      then there are $\pi\le P_1\le P_2$ and an optimal stationary rule that produces for $P<P_1$, inspects for $P_1\le P<P_2$, and revises for $P\ge P_2$. When revision is optimal for at least one admissible belief, $P_2\le1$.
--   2. If
--      $$
--      I+\beta(V_\beta(1)-V_\beta(\pi))\ge\frac{C}{1-\beta(1-\pi)}
--      \quad\text{or}\quad
--      \frac{R-I}{\beta(V_\beta(1)-V_\beta(\pi))}\le\frac{R}{C}(1-\beta(1-\pi)),
--      $$
--      then there is $P_1\ge\pi$ and an optimal stationary rule that produces for $P<P_1$ and revises for $P\ge P_1$, with no inspection interval.
--
--   These conditions distinguish parameter regimes in which a single inspection interval can be selected from those admitting a rule that never inspects.
--
--   **Formalization Note** “Optimal” means that the rule attains the minimum in equation (3) at every $P\in[0,1]$, including threshold points. Part (a)'s printed $P_2\le1$ is false when revision is never optimal; the paper's proof allows an infinite threshold, represented here by $P_2>1$. When $\pi=1$, Lean's quotient with denominator $V_\beta(1)-V_\beta(\pi)=0$ is zero; the implications are still valid in that boundary case.
-- source:
--   Ross, Quality Control under Markovian Deterioration, Management Science 17(9):587–596 (1971), DOI 10.1287/mnsc.17.9.587, pp. 592–593, Theorem 3.7(a,b) and proof

import Definitions.Def_RossQC_Sufficient_Model

namespace RossQC.Sufficient

/-- Ross, Theorem 3.7(a,b), pp. 592–593. A β-optimal stationary rule
selects a minimum of (3) at every admissible belief, including threshold
points. The printed bound `P₂ ≤ 1` in (a) is imposed when the optimal revise
region is nonempty; otherwise `P₂ > 1` allows that interval to be empty, as
the paper's proof explicitly permits. `0 < C` makes the displayed quotient
well-defined. Lean's zero-denominator convention applies when `π = 1`,
where `V_β(1) - V_β(π) = 0`; the two implications retain their intended
conclusions in that case. -/
theorem theorem_3_7 (M : Model)
    (hβ0 : 0 < M.β) (hβ1 : M.β < 1)
    (hπ0 : 0 ≤ M.π) (hπ1 : M.π ≤ 1)
    (hC0 : 0 < M.C) (hCI : M.C < M.I) (hIR : M.I < M.R) :
    ((1 - M.β) * (M.R + M.β * M.value M.π) / M.C ≤
        (M.R - M.I) / (M.β * (M.value 1 - M.value M.π)) →
      ∃ P₁ P₂ : ℝ, M.π ≤ P₁ ∧ P₁ ≤ P₂ ∧
        ((∃ P ∈ Set.Icc (0 : ℝ) 1,
            M.rhs3 M.value P .revise = M.value P) → P₂ ≤ 1) ∧
        ∀ P ∈ Set.Icc (0 : ℝ) 1,
          M.rhs3 M.value P (M.threeRegion P₁ P₂ P) = M.value P) ∧
    ((M.I + M.β * (M.value 1 - M.value M.π) ≥
        M.C / (1 - M.β * (1 - M.π)) ∨
      (M.R - M.I) / (M.β * (M.value 1 - M.value M.π)) ≤
        (M.R / M.C) * (1 - M.β * (1 - M.π))) →
      ∃ P₁ : ℝ, M.π ≤ P₁ ∧
        ∀ P ∈ Set.Icc (0 : ℝ) 1,
          M.rhs3 M.value P (M.twoRegion P₁ P) = M.value P) := by sorry

end RossQC.Sufficient
