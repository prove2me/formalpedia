-- Prove2me | Theorems.Thm_QAOAE3Lin2_General_eq_7_odd
-- name    : QAOAE3Lin2.General.eq_7_odd
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:02:15.661988+00:00
-- url     : https://prove2.me/theorems/7d6906f6-6fc0-4e4f-bdd6-ab60771188ed
-- title:
--   Section II, p. 4 — (7) is an odd function of γ
-- statement:
--   For every Max E3LIN2 instance with $m$ equations and all real $\gamma,\beta$, let $F(\gamma,\beta)$ be the expected number of satisfied equations of the measured state $|\gamma,\beta\rangle$. Then
--   $$F(-\gamma,\beta)=m-F(\gamma,\beta).$$
--
--   Since the quantity (7) at $\gamma$ is $F(-\gamma,\beta)-m/2$, this says exactly that (7) is an odd function of $\gamma$. It is what turns a lower bound on $|(7)|$ into a lower bound on (7) itself, by replacing $\gamma$ with $-\gamma$.
--
--   **Formalization Note.** The identity holds for every $\beta$, as the paper's sentence asserts without restriction on $\beta$.
-- source:
--   Farhi, Goldstone, Gutmann, A Quantum Approximate Optimization Algorithm Applied to a Bounded Occurrence Constraint Problem, arXiv:1412.6062v2, p. 4, Section II, after (7)

import Mathlib
import Definitions.Def_QAOAE3Lin2_General_Setting

namespace QAOAE3Lin2.General

theorem eq_7_odd {n m : ℕ} (tri : Fin m → Fin n × Fin n × Fin n) (rhs : Fin m → Bool)
    (γ β : ℝ) :
    expSat tri rhs (-γ) β = (m : ℝ) - expSat tri rhs γ β := by sorry

end QAOAE3Lin2.General
