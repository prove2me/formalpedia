-- Prove2me | Theorems.Thm_TranscendenceTheory_elliptic_formal_flow_scalar_reduction
-- name    : TranscendenceTheory.elliptic_formal_flow_scalar_reduction
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-14T19:19:28.259319+00:00
-- url     : https://prove2.me/theorems/913db1a6-79e9-4ab1-b6ca-c8f43d6e2d36
-- title:
--   Scalar reduction and conserved cubic of the elliptic formal flow
-- statement:
--   Over any field K of characteristic zero, let g∈K and prescribe four initial values v₀,v₁,v₂,v₃. A family of formal power series J₀,J₁,J₂,J₃ has these initial coefficients and solves
--
--   J₀′=1, J₁′=J₂, J₂′=6J₁²−g/2, J₃′=−J₁
--
--   if and only if it is reconstructed from a single series P satisfying P(0)=v₁, [t]P=v₂, P″=6P²−g/2, and the conserved cubic identity
--
--   (P′)²−4P³+gP = v₂²−4v₁³+gv₁.
--
--   The reconstruction is J₀=v₀+t, J₁=P, J₂=P′, and J₃=v₃−∫₀ᵗP(u)du, where the last expression means the formal series whose coefficient in positive degree k is −[t^{k−1}]P/k. There is no convergence assumption. The conserved identity follows from the second-order equation and the two initial coefficients, including when v₂=0; the proof never divides by P′.
-- source:
--   Derived scalar elliptic formal-flow step for https://prove2.me/theorems/c0d95ff7-a3d1-4c4c-b453-ad81e88f6f79. Mission context: Senthil Kumar K (2026), Algebraic independence of values of Weierstrass elliptic and zeta functions, Appendix A.2, Theorem A.3 and Proposition A.1; https://doi.org/10.1017/S001309152610145X. This is a derived algebraic tool, not a completion of the zero estimate. Primary Lean sources: Mathlib RingTheory/PowerSeries/Derivative.lean, RingTheory/PowerSeries/Basic.lean and RingTheory/Derivation/Basic.lean, revision 0df444a360eaa60ab8c11dca51a86af692955474. Formal integration reconstructs zeta, differentiation reconstructs wp-prime, and the time coordinate is affine. Differentiating the elliptic cubic quantity gives zero, so its value equals its initial value. These identities reduce the four-coordinate flow to one scalar second-order equation without a nonvanishing assumption on the first derivative.

import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

noncomputable section
open scoped Classical

theorem TranscendenceTheory.elliptic_formal_flow_scalar_reduction
    (K : Type*) [Field K] [CharZero K] (g : K) (v : Fin 4 → K)
    (J : Fin 4 → PowerSeries K) :
    let R : PowerSeries K → Fin 4 → PowerSeries K := fun P =>
      ![PowerSeries.C (v 0) + PowerSeries.X, P, PowerSeries.derivative K P,
        PowerSeries.mk fun n =>
          if n = 0 then v 3 else -PowerSeries.coeff (n - 1) P / (n : K)]
    ((∀ a, PowerSeries.coeff 0 (J a) = v a) ∧
      PowerSeries.derivative K (J 0) = 1 ∧
      PowerSeries.derivative K (J 1) = J 2 ∧
      PowerSeries.derivative K (J 2) =
        PowerSeries.C 6 * (J 1) ^ 2 - PowerSeries.C (g / 2) ∧
      PowerSeries.derivative K (J 3) = -J 1) ↔
    ∃ P : PowerSeries K,
      PowerSeries.coeff 0 P = v 1 ∧ PowerSeries.coeff 1 P = v 2 ∧
      PowerSeries.derivative K (PowerSeries.derivative K P) =
        PowerSeries.C 6 * P ^ 2 - PowerSeries.C (g / 2) ∧
      (PowerSeries.derivative K P) ^ 2 - PowerSeries.C 4 * P ^ 3 +
        PowerSeries.C g * P =
          PowerSeries.C ((v 2) ^ 2 - 4 * (v 1) ^ 3 + g * v 1) ∧
      J = R P := by sorry
