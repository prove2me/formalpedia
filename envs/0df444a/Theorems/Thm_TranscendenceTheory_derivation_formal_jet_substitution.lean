-- Prove2me | Theorems.Thm_TranscendenceTheory_derivation_formal_jet_substitution
-- name    : TranscendenceTheory.derivation_formal_jet_substitution
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-14T17:31:36.736295+00:00
-- url     : https://prove2.me/theorems/5ce4133e-3103-4283-a93b-f003cd47f11e
-- title:
--   Formal Taylor substitution for an algebraic derivation
-- statement:
--   Let K be any field of characteristic zero, σ any variable type, D a K-linear derivation of K[σ], and v a point with coordinates in K. For each variable i form the formal series J_i(t)=Σ_{k≥0} ev_v(D^k X_i)t^k/k!. For every polynomial p and natural n, the coefficient of t^n in p(J_i(t)) multiplied by n! equals ev_v(D^n p).
--
--   Thus substitution into the coordinate series recovers every algebraic jet, including jets of products and powers. This is a formal-series identity, with no convergence assertion or analytic hypothesis. No finiteness assumption on σ is needed, and n=0 is included.
-- source:
--   Derived formal Taylor substitution step for https://prove2.me/theorems/69db451e-8f1e-466d-8647-98d2545c7cb3. Mission context: Senthil Kumar K (2026), Algebraic independence of values of Weierstrass elliptic and zeta functions, Appendix A.2, Theorem A.3 and Proposition A.1; https://doi.org/10.1017/S001309152610145X. This is an algebraic tool for the formal development, not a completion of the zero estimate. Primary Lean sources: Mathlib RingTheory/Derivation/Basic.lean, Data/Nat/Choose/Sum.lean, Data/Nat/Choose/Cast.lean and RingTheory/PowerSeries/Basic.lean, revision 0df444a360eaa60ab8c11dca51a86af692955474. The iterated Leibniz rule and factorial normalization identify polynomial substitution into the coordinate formal series with all iterated derivation jets. Invertible factorial rescaling preserves the finite interpolation obstruction exactly.

import Mathlib.Algebra.MvPolynomial.Derivation
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp

noncomputable section
open scoped Classical

theorem TranscendenceTheory.derivation_formal_jet_substitution
    (K σ : Type*) [Field K] [CharZero K]
    (D : Derivation K (MvPolynomial σ K) (MvPolynomial σ K)) (v : σ → K)
    (p : MvPolynomial σ K) (n : ℕ) :
    let J : σ → PowerSeries K := fun i => PowerSeries.mk fun k =>
      MvPolynomial.eval v (D^[k] (MvPolynomial.X i)) / (k.factorial : K)
    (n.factorial : K) * PowerSeries.coeff n (MvPolynomial.aeval J p) =
      MvPolynomial.eval v (D^[n] p) := by sorry
