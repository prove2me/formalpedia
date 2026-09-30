-- Prove2me | Theorems.Thm_TranscendenceTheory_derivation_formal_flow_unique
-- name    : TranscendenceTheory.derivation_formal_flow_unique
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-14T18:31:42.830685+00:00
-- url     : https://prove2.me/theorems/b5582c83-7439-4307-931b-13a4433bf968
-- title:
--   Existence and uniqueness of formal polynomial flows
-- statement:
--   Let K be a field of characteristic zero, let D be a K-linear derivation of the polynomial ring K[σ] for any variable type σ, and fix initial coordinates v : σ → K. The formal series J_i(t)=Σ_{k≥0} ev_v(D^k X_i)t^k/k! have initial coefficients v_i and satisfy J_i'=ev_J(DX_i). They are the unique family of formal power series satisfying these initial conditions and polynomial differential equations.
--
--   There is no finiteness assumption on σ and no degree restriction on D. This is a formal power-series result, with no convergence assertion. Characteristic zero permits the coefficient recurrence to be solved uniquely by dividing by each positive integer.
-- source:
--   Derived formal ODE step for https://prove2.me/theorems/8bca4fbc-160b-4113-a9a7-68082ea63fd2. Mission context: Senthil Kumar K (2026), Algebraic independence of values of Weierstrass elliptic and zeta functions, Appendix A.2, Theorem A.3 and Proposition A.1; https://doi.org/10.1017/S001309152610145X. This is a derived algebraic tool for the formal development, not a completion of the zero estimate. Uses the accepted theorem https://prove2.me/theorems/5ce4133e-3103-4283-a93b-f003cd47f11e. Primary Lean sources: Mathlib RingTheory/PowerSeries/Derivative.lean, RingTheory/PowerSeries/Basic.lean and Algebra/MvPolynomial/Derivation.lean, revision 0df444a360eaa60ab8c11dca51a86af692955474. Canonical derivation jets solve the polynomial ODE, and coefficient induction proves uniqueness. The explicit chart-0 equations and initial values therefore determine exactly the formal series in the parent obstruction.

import Theorems.Thm_TranscendenceTheory_derivation_formal_jet_substitution
import Mathlib.RingTheory.PowerSeries.Derivative

noncomputable section
open scoped Classical

theorem TranscendenceTheory.derivation_formal_flow_unique
    (K σ : Type*) [Field K] [CharZero K]
    (D : Derivation K (MvPolynomial σ K) (MvPolynomial σ K)) (v : σ → K) :
    let J : σ → PowerSeries K := fun i => PowerSeries.mk fun k =>
      MvPolynomial.eval v (D^[k] (MvPolynomial.X i)) / (k.factorial : K)
    (∀ i, PowerSeries.coeff 0 (J i) = v i) ∧
    (∀ i, PowerSeries.derivative K (J i) =
      MvPolynomial.aeval J (D (MvPolynomial.X i))) ∧
    ∀ H : σ → PowerSeries K,
      (∀ i, PowerSeries.coeff 0 (H i) = v i) →
      (∀ i, PowerSeries.derivative K (H i) =
        MvPolynomial.aeval H (D (MvPolynomial.X i))) → H = J := by sorry
