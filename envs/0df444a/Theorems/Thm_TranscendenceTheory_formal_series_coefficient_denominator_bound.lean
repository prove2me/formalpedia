-- Prove2me | Theorems.Thm_TranscendenceTheory_formal_series_coefficient_denominator_bound
-- name    : TranscendenceTheory.formal_series_coefficient_denominator_bound
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-14T21:56:34.475051+00:00
-- url     : https://prove2.me/theorems/0dda94ea-c973-4948-837c-e170200ce39f
-- title:
--   Degree bounds after clearing formal-series denominators
-- statement:
--   Let R and S be commutative rings, let φ:R[z]→S be a ring homomorphism, and let Q,V∈R[z][[x]] and E∈S[[x]]. Apply φ coefficientwise to formal series, and suppose
--
--   $$\varphi(Q)E=\varphi(V).$$
--
--   Write Qᵢ=[xⁱ]Q, Vᵢ=[xⁱ]V and Eᵢ=[xⁱ]E. Suppose a,b are nonnegative integers such that every Qᵢ has polynomial degree at most b and every Vᵢ has degree at most a. Then, for every nonnegative integer k, there is a polynomial Pₖ∈R[z] such that
--
--   $$\deg P_k\le a+kb,\qquad \varphi(Q_0)^{k+1}E_k=\varphi(P_k).$$
--
--   The degree bound uses natural degree, with the zero polynomial assigned degree zero. The map φ need not be injective, φ(Q₀) need not be invertible, and neither ring is required to be a domain.
--
--   This bounds the polynomial numerator of a formal coefficient after clearing the indicated power of the constant denominator. If φ(Q₀) is a unit, it gives a rational expression for Eₖ with denominator φ(Q₀)ᵏ⁺¹.
-- source:
--   Derived local-jet denominator bound for https://prove2.me/theorems/ab7fdc61-66fb-4ce3-9d85-5a97824ecb33. Mission context: Senthil Kumar K (2026), Algebraic independence of values of Weierstrass elliptic and zeta functions, Appendix A.2, Theorem A.3 and Proposition A.1; https://doi.org/10.1017/S001309152610145X. This is an algebraic tool for the interpolation frontier; the geometric zero estimate remains open. Primary Lean sources: Mathlib RingTheory/PowerSeries/Basic.lean (coefficient convolution and map), Inverse.lean (mul_invOfUnit), Algebra/Polynomial/Degree/Defs.lean and BigOperators.lean (degree bounds for sums, products and powers), revision 0df444a360eaa60ab8c11dca51a86af692955474. See https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Polynomial/Degree/Operations.html. Strong induction on coefficients clears denominators and bounds each numerator degree by a+k*b. The local-jet specialization has a=1, b=2 and a quadratic denominator with constant coefficient one. All interpolation witnesses, weights and numerical bounds are preserved.

import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

open PowerSeries

theorem TranscendenceTheory.formal_series_coefficient_denominator_bound
    (R S : Type*) [CommRing R] [CommRing S]
    (φ : Polynomial R →+* S) (Q V : PowerSeries (Polynomial R))
    (E : PowerSeries S) (a b : ℕ)
    (h : PowerSeries.map φ Q * E = PowerSeries.map φ V)
    (hQ : ∀ k, (PowerSeries.coeff k Q).natDegree ≤ b)
    (hV : ∀ k, (PowerSeries.coeff k V).natDegree ≤ a) (k : ℕ) :
    ∃ P : Polynomial R, P.natDegree ≤ a + k * b ∧
      φ (PowerSeries.coeff 0 Q) ^ (k + 1) * PowerSeries.coeff k E = φ P := by sorry
