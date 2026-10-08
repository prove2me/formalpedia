-- Prove2me | Theorems.Thm_TimeInconsLQ_Deterministic_proposition_4_1
-- name    : TimeInconsLQ.Deterministic.proposition_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T13:25:06.056493+00:00
-- url     : https://prove2.me/theorems/e0906978-b1b0-4e07-a369-8a8cafbc4546
-- title:
--   Proposition 4.1 — a positive solution (M, J) of (4.10) gives the positive solution (M, M/J) of (4.9)
-- statement:
--   Consider the scalar-state problem with deterministic coefficients of §4 and the coupled Riccati systems (4.9) for $(M,N)$ and (4.10) for $(M,J)$ on $[0,T]$.
--
--   **Proposition 4.1.** If the system (4.10) admits a positive solution pair $(M,J)$ on $[0,T]$, then
--   $$\Big(M,\ \frac MJ\Big)$$
--   is a positive solution pair of the system (4.9) on $[0,T]$.
--
--   The substitution $J=M/N$ removes the quadratic term $N^2$ from the $N$-equation; this proposition transfers solvability of the better-behaved system (4.10) back to (4.9), which determines the equilibrium feedback.
--
--   **Formalization Note.** Solutions are in integral form on $[0,T]$ and include invertibility of $R_s+M_sD_s'D_s$ there (see the `Riccati` module). The statement needs none of the standing assumptions, so none is imposed.
-- source:
--   Hu, Jin, Zhou, Time-Inconsistent Stochastic Linear–Quadratic Control, arXiv:1111.0818v1, p. 10, Proposition 4.1

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_TimeInconsLQ_Deterministic_Model
import Definitions.Def_TimeInconsLQ_Deterministic_Riccati

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open scoped ENNReal NNReal

namespace TimeInconsLQ.Deterministic

/-- Proposition 4.1 (p. 10): if `(M, J)` is a positive solution pair of (4.10) on `[0, T]`, then
`(M, M/J)` is a positive solution pair of (4.9) on `[0, T]`. -/
theorem proposition_4_1 {l d : ℕ} (c : Coeffs l d) (T : ℝ≥0) (M J : ℝ≥0 → ℝ)
    (hMJ : IsPosSol410 c T M J) :
    IsPosSol49 c T M (fun s => M s / J s) := by sorry

end TimeInconsLQ.Deterministic
