-- Prove2me | Theorems.Thm_QAOAE3Lin2_Typical_eq_55
-- name    : QAOAE3Lin2.Typical.eq_55
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T10:59:16.97247+00:00
-- url     : https://prove2.me/theorems/ff5d2d9e-02be-4d27-8a47-fd1de21fa5c7
-- title:
--   Section III, (55), p. 11 — at β = π/4 the expected satisfied count of |−γ, π/4⟩ is m/2 + Σ ½ d_abc ⟨Z_aZ_bZ_c⟩
-- statement:
--   Fix an instance of E3LIN2 with $m$ equations (any triples, any right-hand sides) and an angle $\gamma\in\mathbb R$. Measure the level-one QAOA state $|-\gamma,\pi/4\rangle$ in the computational basis. The expected number of satisfied equations equals $m/2$ plus the sum, over the equations, of their clause terms:
--   $$\mathbb E[\#\text{satisfied}]=\frac m2+\sum_{a<b<c}\tfrac12\,d_{abc}\,\langle-\gamma,\pi/4|Z_aZ_bZ_c|-\gamma,\pi/4\rangle .$$
--   Equivalently, the target (7) at $\beta=\pi/4$, $\langle-\gamma,\pi/4|C|-\gamma,\pi/4\rangle$ with $C$ as in (6), is the sum of the $m$ clause terms.
--
--   This identity reduces the analysis of the whole instance to one equation at a time; both the mean bound (50) and the variance bound of Section III start from it.
--
--   **Formalization Note** The left side is the expected number of satisfied equations; subtracting $m/2$ gives the paper's (7). The sum runs over the equations $i=1,\dots,m$, which is the paper's sum over the triples with $d_{abc}\neq0$.
-- source:
--   Farhi, Goldstone, Gutmann, A Quantum Approximate Optimization Algorithm Applied to a Bounded Occurrence Constraint Problem, arXiv:1412.6062v2, p. 11, Section III, (55) (with p. 4, (6) and after (7))

import Mathlib
import Definitions.Def_QAOAE3Lin2_Typical_Setting

namespace QAOAE3Lin2.Typical

/-- (55), p. 11 (with (6) and p. 4): at `β = π/4` the expected number of satisfied equations of
`|−γ, π/4⟩` is `m/2` plus the sum over the equations of `½ d_abc ⟨Z_a Z_b Z_c⟩`. -/
theorem eq_55 {n m : ℕ} (tri : Fin m → Fin n × Fin n × Fin n) (rhs : Fin m → Bool) (γ : ℝ) :
    QAOAE3Lin2.General.expSat tri rhs (-γ) (Real.pi / 4) = (m : ℝ) / 2 + ∑ i, clauseTerm tri rhs i γ := by sorry

end QAOAE3Lin2.Typical
