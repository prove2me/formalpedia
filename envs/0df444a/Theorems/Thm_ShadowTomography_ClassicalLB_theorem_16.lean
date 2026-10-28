-- Prove2me | Theorems.Thm_ShadowTomography_ClassicalLB_theorem_16
-- name    : ShadowTomography.ClassicalLB.theorem_16
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T17:28:04.025128+00:00
-- url     : https://prove2.me/theorems/148335b6-1fdf-42a2-835e-5db20b4586e5
-- title:
--   Theorem 16: classical shadow-tomography lower bound
-- statement:
--   There are universal constants $c>0$ and $N_0$ such that, whenever $D\ge N_0$, $\log_2 M\ge N_0$, and $0<\varepsilon\le1/6$, one can choose $M$ diagonal two-outcome measurements $E_1,\ldots,E_M$ on a $D$-dimensional system. Each diagonal entry of each $E_i$ is $0$ or $1$, as for the Boolean tests in Section 6.1. Every measurement procedure on $k$ copies that, for **every diagonal mixed state** $\rho$, estimates all $\operatorname{Tr}(E_i\rho)$ within $\varepsilon$ with probability at least $2/3$ must use
--
--   $$
--   k\ge c\,\frac{\min\{D,\log_2 M\}}{\varepsilon^2}.
--   $$
--
--   This establishes Theorem 16 in its classical special case, and therefore also rules out a smaller uniform copy count for the unrestricted quantum task.
--
--   **Formalization Note** A procedure is a finite-outcome POVM on $\rho^{\otimes k}$ with a real estimate vector attached to each outcome. Allowing estimates outside $[0,1]$ is equivalent for this lower bound, since clipping them to $[0,1]$ cannot increase error. The thresholds and $\varepsilon\le1/6$ make the asymptotic and probability claims meaningful; they are disclosed additions to the paper's theorem sentence.
-- source:
--   Aaronson, Shadow Tomography of Quantum States, arXiv:1711.01053v2, p. 20, Theorem 16; pp. 20–21, proof

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_ShadowTomography_ClassicalLB_IsEffect
import Definitions.Def_ShadowTomography_ClassicalLB_tensorPow
import Definitions.Def_ShadowTomography_ClassicalLB_POVM

namespace ShadowTomography.ClassicalLB

/-- Theorem 16, including its classical-special-case assertion, stated for all finite
outcome measurements on the copied state. -/
theorem theorem_16 :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ (D M : ℕ) (ε : ℝ),
      N₀ ≤ D → (N₀ : ℝ) ≤ Real.logb 2 M → 0 < ε → ε ≤ 1 / 6 →
      ∃ E : Fin M → Matrix (Fin D) (Fin D) ℂ,
            (∀ i, IsEffect (E i) ∧ (E i).IsDiag ∧
              ∀ x : Fin D, (E i) x x = 0 ∨ (E i) x x = 1) ∧
        ∀ (k : ℕ) (Ω : Type) [Fintype Ω]
          (P : POVM Ω (Fin k → Fin D)) (b : Ω → Fin M → ℝ),
          (∀ ρ : Matrix (Fin D) (Fin D) ℂ,
            WildeQIT.IsDensityOperator ρ → ρ.IsDiag →
              (2 / 3 : ℝ) ≤ P.prob (tensorPow ρ k)
                (fun ω => ∀ i, |b ω i - ((E i) * ρ).trace.re| ≤ ε)) →
          c * min (D : ℝ) (Real.logb 2 M) / ε ^ 2 ≤ (k : ℝ) := by sorry

end ShadowTomography.ClassicalLB
