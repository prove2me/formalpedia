-- Prove2me | Theorems.Thm_QAlgorithms_Arunachalam_max_c_div_sqrt_pow
-- name    : QAlgorithms.Arunachalam.max_c_div_sqrt_pow
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-13T17:55:24.480331+00:00
-- url     : https://prove2.me/theorems/aec45c5c-1b42-4d34-beb7-b77cf00bd54c
-- title:
--   The maximum of (c/√t)^t on [1, c²] is e^{c²/(2e)} (for c ≥ √e)
-- statement:
--   Let $c\ge\sqrt e$. Then the function $t\mapsto(c/\sqrt t)^t$ attains its maximum over the interval $[1,c^2]$, and
--
--   $$
--   \max\{(c/\sqrt t)^t: t\in[1,c^2]\}=e^{c^2/(2e)}.
--   $$
--
--   The maximiser is $t=c^2/e$. The bound is used to control terms of the form $(c/\sqrt t)^t$ in the analysis of the PGM for the PAC and agnostic hard instances.
--
--   **Formalization Note** The source states the claim without a range for $c$; it is false for $c<\sqrt e$ (for $c=1$ the set is $\{1\}$ while $e^{1/(2e)}>1$). The hypothesis $c\ge\sqrt e$ is exactly the condition under which the proof's maximiser $c^2/e$ lies in $[1,c^2]$. The maximum is stated as `IsGreatest` of the image set, so attainment is part of the statement.
-- source:
--   Srinivasan Arunachalam, Quantum Algorithms and Learning Theory — Part II, 2018 thesis, ILLC DS-2018-08, PDF p. 162, Claim 7.3.6. https://ir.cwi.nl/pub/27536/Thesis_S_Arunachalam

import Definitions.Def_QAlgorithms_Defs_BooleanFourier
set_option autoImplicit false

namespace QAlgorithms.Arunachalam



/-- Arunachalam p.162, Claim 7.3.6: `max {(c/√t)^t : t ∈ [1, c²]} = e^{c²/(2e)}`.

Corrected statement (trap 30): the source states it for unspecified `c`; it is false for
`c < √e` (at `c = 1` the set is `{1}`, while `e^{1/(2e)} > 1`; for `|c| < 1` the interval is
empty). The source's proof places the maximiser at `t = c²/e`, which lies in `[1, c²]` exactly
when `c² ≥ e`; we therefore assume `√e ≤ c`. -/
theorem max_c_div_sqrt_pow {c : ℝ} (hc : Real.sqrt (Real.exp 1) ≤ c) :
    IsGreatest ((fun t : ℝ => (c / Real.sqrt t) ^ t) '' Set.Icc 1 (c ^ 2))
      (Real.exp (c ^ 2 / (2 * Real.exp 1))) := by
  sorry




end QAlgorithms.Arunachalam
