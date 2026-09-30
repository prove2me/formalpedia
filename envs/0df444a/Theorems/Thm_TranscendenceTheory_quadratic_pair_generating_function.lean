-- Prove2me | Theorems.Thm_TranscendenceTheory_quadratic_pair_generating_function
-- name    : TranscendenceTheory.quadratic_pair_generating_function
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-14T21:15:36.801952+00:00
-- url     : https://prove2.me/theorems/d99bcab3-0103-4fe8-acc7-2d70d93d5717
-- title:
--   Rational generating functions for quadratic-pair recurrences
-- statement:
--   Let R be any commutative ring and let d,a,b∈R. Define (u₀,v₀)=(1,0) and
--
--   $$u_{n+1}=a u_n+dbv_n,\qquad v_{n+1}=b u_n+a v_n.$$
--
--   In the formal power-series ring R[[z]], put Q(z)=1−2az+(a²−db²)z². Its constant coefficient is 1, so it has a formal inverse H. Then
--
--   $$\sum_{n\ge0}u_nz^n=(1-az)H(z),\qquad
--   \sum_{n\ge0}v_nz^n=bzH(z).$$
--
--   These are identities of formal series. They require no analytic convergence, characteristic-zero assumption, field structure, or invertibility of a,b,d, or a²−db². The Lean statement uses PowerSeries.invOfUnit Q 1 for H.
-- source:
--   Derived rational generating-function step for https://prove2.me/theorems/59116160-e6c2-4b88-a7be-752c2121d583. Mission context: Senthil Kumar K (2026), Algebraic independence of values of Weierstrass elliptic and zeta functions, Appendix A.2, Theorem A.3 and Proposition A.1; https://doi.org/10.1017/S001309152610145X. This is an algebraic tool for the interpolation frontier; the geometric zero estimate remains open. Primary Lean sources: Mathlib RingTheory/PowerSeries/Basic.lean and Inverse.lean, especially coefficient shifts and invOfUnit, revision 0df444a360eaa60ab8c11dca51a86af692955474. The pair recurrence gives two first-order series equations. Eliminating the coupled terms yields a common quadratic denominator with constant coefficient one. Its formal inverse reconstructs both coefficient sequences. The frontier keeps its local jet variable distinct from the generating variable and preserves every witness, weight and numerical bound.

import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Tactic.LinearCombination

open PowerSeries

theorem TranscendenceTheory.quadratic_pair_generating_function
    (R : Type*) [CommRing R] (d a b : R) :
    let T : ℕ → R × R := Nat.rec (1, 0)
      (fun _ t => (a * t.1 + d * b * t.2, b * t.1 + a * t.2))
    let Q : PowerSeries R := 1 - C (2 * a) * X + C (a ^ 2 - d * b ^ 2) * X ^ 2
    let H := PowerSeries.invOfUnit Q (1 : Rˣ)
    PowerSeries.mk (fun n => (T n).1) = (1 - C a * X) * H ∧
      PowerSeries.mk (fun n => (T n).2) = C b * X * H := by sorry
