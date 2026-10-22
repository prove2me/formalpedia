-- Prove2me | Theorems.Thm_RobustOpt2009_CQApproximation_matrix_cube
-- name    : RobustOpt2009.CQApproximation.matrix_cube
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-22T03:44:04.730369+00:00
-- url     : https://prove2.me/theorems/e7c79011-67b7-409b-a2e4-def9aa8f69ea
-- title:
--   Theorem 7.1.3 — the real mixed matrix cube theorem
-- statement:
--   There is a universal nondecreasing function $\vartheta$ of the integer rank parameter such that
--   $$\vartheta(2)=\frac\pi2,\qquad\vartheta(4)=2,\qquad\vartheta(\mu)\le\pi\sqrt{\mu/2}\quad(\mu\ge2).$$
--   For every positive matrix dimension, symmetric data and full-block factors in the mixed cube model, and every $\rho>0$:
--
--   1. $\mathcal B(\rho)$ implies $\mathcal A(\rho)$. If there is exactly one block in total, these conditions are equivalent.
--   2. If $\operatorname{rank}(B_i)\le\mu$ for every scalar block, where $\mu\ge2$, then
--   $$\neg\mathcal B(\rho)\quad\Longrightarrow\quad\neg\mathcal A(\vartheta(\mu)\rho).$$
--   The full-block matrices have no rank restriction. The result bounds conservatism by inflation of the uncertainty radius.
--
--   **Formalization Note** The existential quantifier for $\vartheta$ precedes all dimensions and data, so it cannot depend on an instance. It is extended monotonically to natural arguments 0 and 1, where no bound is used. Either block family can be empty. The square root contains the quotient $\mu/2$, as printed, rather than placing the division outside the square root.
-- source:
--   Ben-Tal, El Ghaoui and Nemirovski, Robust Optimization, Princeton University Press, 2009, DOI 10.1515/9781400831050, Theorem 7.1.3, printed p. 183 (PDF p. 209).

import Definitions.Def_RobustOpt2009_CQApproximation_MixedCube

namespace RobustOpt2009.CQApproximation

/-- Theorem 7.1.3, printed p. 183, PDF p. 209. The universal function is
quantified before all dimensions and problem data. -/
theorem matrix_cube :
    ∃ ϑ : ℕ → ℝ, Monotone ϑ ∧ ϑ 2 = Real.pi / 2 ∧ ϑ 4 = 2 ∧
      (∀ μ : ℕ, 2 ≤ μ → ϑ μ ≤ Real.pi * Real.sqrt ((μ : ℝ) / 2)) ∧
      ∀ (m p q : ℕ), 0 < m → ∀ (D : CubeData m p q) (ρ : ℝ), 0 < ρ →
        (D.Envelope ρ → D.Robust ρ) ∧
        (p + q = 1 → (D.Envelope ρ ↔ D.Robust ρ)) ∧
        (∀ μ : ℕ, 2 ≤ μ → (∀ i, (D.B i).rank ≤ μ) →
          ¬ D.Envelope ρ → ¬ D.Robust (ϑ μ * ρ)) := by sorry

end RobustOpt2009.CQApproximation
