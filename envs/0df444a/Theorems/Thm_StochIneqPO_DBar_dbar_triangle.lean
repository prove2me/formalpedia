-- Prove2me | Theorems.Thm_StochIneqPO_DBar_dbar_triangle
-- name    : StochIneqPO.DBar.dbar_triangle
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:36:49.498922+00:00
-- url     : https://prove2.me/theorems/d1229e92-3b55-44d1-acb7-a9984edbebd5
-- title:
--   Proof of Theorem 8, p. 910 — triangle inequality for d̄ (asserted: "d̄ is a distance")
-- statement:
--   Let $P,Q,R$ be stationary laws of real-valued two-sided processes on $\Omega=\mathbb R^{\mathbb Z}$, each with an integrable time-zero coordinate $\omega^0$. Ornstein's distance $\bar d$ (the infimum of $\int|\omega_1^0-\omega_2^0|\,d\nu$ over shift-invariant couplings $\nu$) satisfies the triangle inequality
--
--   $$\bar d(P,Q)\le\bar d(P,R)+\bar d(R,Q).$$
--
--   The proof of Theorem 8 uses this inequality, with $R$ a stationary law below both $P$ and $Q$, to obtain the inequality "$\le$" in (18). The paper justifies it only by the remark that $\bar d$ is a distance and gives no proof.
--
--   **Formalization Note** The statement is posed for all stationary $R$ with integrable $\omega^0$. The paper's display only needs it for $R\prec P$, $R\prec Q$. The integrability hypotheses are the standing assumption of Section 8, which makes all three infima finite.
-- source:
--   Kamae, Krengel, O'Brien, Stochastic Inequalities on Partially Ordered Spaces, Ann. Probab. 5 (1977), proof of Theorem 8, p. 910 (PDF p. 12), display 'd̄(P, Q) ≤ d̄(P, R) + d̄(R, Q) (since d̄ is a distance)'

import Mathlib
import Definitions.Def_StochIneqPO_DBar_IsShiftInvariant
import Definitions.Def_StochIneqPO_DBar_dbar

namespace StochIneqPO.DBar

open MeasureTheory

/-- Proof of Theorem 8, p. 910 (asserted): `d̄` satisfies the triangle inequality. -/
theorem dbar_triangle
    (P Q R : Measure (ℤ → ℝ))
    (hP : IsShiftInvariant P) (hQ : IsShiftInvariant Q) (hR : IsShiftInvariant R)
    (hPi : Integrable (fun ω : ℤ → ℝ => ω 0) P)
    (hQi : Integrable (fun ω : ℤ → ℝ => ω 0) Q)
    (hRi : Integrable (fun ω : ℤ → ℝ => ω 0) R) :
    dbar P Q ≤ dbar P R + dbar R Q := by sorry

end StochIneqPO.DBar
