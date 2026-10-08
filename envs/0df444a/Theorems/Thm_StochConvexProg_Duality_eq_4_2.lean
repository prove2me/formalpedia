-- Prove2me | Theorems.Thm_StochConvexProg_Duality_eq_4_2
-- name    : StochConvexProg.Duality.eq_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:16:55.881294+00:00
-- url     : https://prove2.me/theorems/a1f6458c-387e-4ef0-a94c-48ef3ddbbab4
-- title:
--   (4.2) — φ**(0) = sup D
-- statement:
--   Under the standing assumptions, with $\sigma$ a probability measure, the biconjugate of the perturbation function with respect to the pairing (1.6), evaluated at $0$, equals the optimal value of the dual:
--   $$\varphi^{**}(0)=\sup\mathbf D=\sup_{y\in Y}\inf_{x\in X}L(x,y).$$
--
--   Together with $\varphi(0)=\inf\mathbf P$ (which holds by definition), it reduces the duality statement $\inf\mathbf P=\sup\mathbf D$ to $\varphi^{**}(0)=\varphi(0)$.
--
--   **Formalization Note** No boundedness of $C_1,C_2$ is assumed. The companion identity (4.3), $\varphi(0)=\inf\mathbf P$, is true by definition in this formalization and is not posed.
-- source:
--   Rockafellar and Wets, Stochastic convex programming: basic duality, Pacific J. Math. 62(1) (1976), p. 188, display (4.2)

import Mathlib
import Definitions.Def_StochConvexProg_Duality_Problem
import Definitions.Def_StochConvexProg_Duality_Dual

open MeasureTheory

namespace StochConvexProg.Duality

/-- Rockafellar–Wets (1976), p. 188, (4.2): `φ**(0) = sup D`. -/
theorem eq_4_2 {S : Type*} [MeasurableSpace S] {σ : Measure S}
    [IsProbabilityMeasure σ] {n₁ n₂ m₁ m₂ : ℕ} (pr : Problem S σ n₁ n₂ m₁ m₂) :
    biconjU pr.phi 0 = pr.supD := by sorry

end StochConvexProg.Duality
