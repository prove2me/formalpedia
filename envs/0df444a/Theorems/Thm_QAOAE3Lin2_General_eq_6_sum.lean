-- Prove2me | Theorems.Thm_QAOAE3Lin2_General_eq_6_sum
-- name    : QAOAE3Lin2.General.eq_6_sum
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:02:24.176837+00:00
-- url     : https://prove2.me/theorems/66256ded-6cb7-448f-8106-8e3705644041
-- title:
--   Section II, (6) and p. 4 — the expected satisfied count is m/2 + Σᵢ ½dᵢ⟨Z_aZ_bZ_c⟩
-- statement:
--   Let an instance of Max E3LIN2 with $m$ equations be given, with signs $d_i\in\{\pm1\}$, and let $|\gamma,\beta\rangle$ be the level-one QAOA state. For all real $\gamma,\beta$, the expected number of satisfied equations when $|\gamma,\beta\rangle$ is measured is
--   $$\sum_x|\langle x|\gamma,\beta\rangle|^2C(x)=\frac m2+\sum_{i=1}^m\tfrac12d_i\,\langle\gamma,\beta|Z_{a_i}Z_{b_i}Z_{c_i}|\gamma,\beta\rangle ,$$
--   where $(a_i,b_i,c_i)$ is the triple of equation $i$.
--
--   This is the operator identity $C=\tfrac m2+\tfrac12\sum d_{abc}Z_aZ_bZ_c$ of (5)–(6) taken in expectation. It reduces the analysis to one clause at a time.
--
--   **Formalization Note.** No hypothesis on the instance is needed. The right side uses that the state is a unit vector.
-- source:
--   Farhi, Goldstone, Gutmann, A Quantum Approximate Optimization Algorithm Applied to a Bounded Occurrence Constraint Problem, arXiv:1412.6062v2, pp. 3–4, Section II, (5)–(6) and p. 4, after (7)

import Mathlib
import Definitions.Def_QAOAE3Lin2_General_Setting

namespace QAOAE3Lin2.General

theorem eq_6_sum {n m : ℕ} (tri : Fin m → Fin n × Fin n × Fin n) (rhs : Fin m → Bool)
    (γ β : ℝ) :
    expSat tri rhs γ β = (m : ℝ) / 2 + ∑ i, (1 / 2) * sgn rhs i * corr tri rhs i γ β := by sorry

end QAOAE3Lin2.General
