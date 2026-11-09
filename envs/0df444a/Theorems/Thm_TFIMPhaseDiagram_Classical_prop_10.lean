-- Prove2me | Theorems.Thm_TFIMPhaseDiagram_Classical_prop_10
-- name    : TFIMPhaseDiagram.Classical.prop_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T13:04:09.320264+00:00
-- url     : https://prove2.me/theorems/4eb59070-9bb4-4218-9454-243dee24f41d
-- title:
--   Proposition 10 — Additive Trotter error with C = 15
-- statement:
--   Let $J$ be symmetric, $h$ real, $\eta_i\ge0$, and $O$ any Pauli string. Write $c=\|J\|_\infty+\|h\|_\infty+\|\eta\|_\infty$, using the row-sum matrix norm. For $0<\epsilon<1$ and $M\ge3$ satisfying the exact bound
--   $$M\ge15\max\{nc/\epsilon,\sqrt{(nc)^3/\epsilon}\},$$
--   one has
--   $$\left|\frac{\operatorname{Tr}(OQ_M)}{\operatorname{Tr}(Q_M)}-\operatorname{Tr}(O\rho)\right|\le\epsilon.$$
--   This is the additive Trotter guarantee needed for arbitrary Pauli observables. The numerical constant is exactly $15$.
--
--   Differences from the source:
--   - encoding: absolute value of a trace difference → complex norm on the trace difference; reason: The intermediate Trotter trace need not be real; the norm is its complex modulus.
-- source:
--   Thuy-Duong (June) Vuong, A computational phase diagram for the transverse field Ising model, STOC 2027 submission #739 (October 2026), canonical source.pdf SHA256 02138c3ee0da2e11c9830e41e823dc009b55592cecb60f77602c2a404f2ecfc7, printed p.7 = PDF p.7, Proposition 10

import Definitions.Def_TFIMPhaseDiagram_Classical_traceSetup

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped BigOperators
noncomputable section

namespace TFIMPhaseDiagram.Classical
/-- Proposition 10, p.7: C=15, without changing the source mesh bound. -/
theorem prop_10 {n : ℕ} (hn : 0 < n) (J : Matrix (Fin n) (Fin n) ℝ)
    (hJ : J.IsSymm) (h η : Fin n → ℝ) (hη : ∀ i, 0 ≤ η i)
    (P : Fin n → Pauli) (ε : ℝ) (hε : 0 < ε ∧ ε < 1)
    (M : ℕ) (hM : 3 ≤ M)
    (hmesh : let c := rowNorm J + maxField h + maxField η
      (M : ℝ) ≥ 15 * max ((n : ℝ)*c/ε) (Real.sqrt (((n : ℝ)*c)^3/ε))) :
  ‖Matrix.trace (pauliString P * trotter J h η M) / Matrix.trace (trotter J h η M) -
    Matrix.trace (pauliString P * density J h η)‖ ≤ ε := by sorry
end TFIMPhaseDiagram.Classical
