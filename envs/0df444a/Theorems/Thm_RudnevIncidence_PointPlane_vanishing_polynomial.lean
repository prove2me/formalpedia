-- Prove2me | Theorems.Thm_RudnevIncidence_PointPlane_vanishing_polynomial
-- name    : RudnevIncidence.PointPlane.vanishing_polynomial
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:16:41.995977+00:00
-- url     : https://prove2.me/theorems/d00137e0-becf-432c-b1bc-fa9e371137dc
-- title:
--   §5, pp. 15–16 — a nonzero homogeneous polynomial of degree d vanishes on any set X ⊂ P³ with C(d+3, 3) > |X|
-- statement:
--   Let $X$ be a finite set of points of $\mathbb P^3$ over a field $\mathbb F$, and $d\ge0$ an integer with
--   $$\binom{d+3}{3}>|X|.$$
--   Then there is a nonzero homogeneous polynomial $Q\in\mathbb F[x_0,x_1,x_2,x_3]$ of degree $d$ vanishing at every point of $X$.
--
--   The proof of Theorem 12 uses it to put all the lines of a random subfamily on a surface of controlled degree.
--
--   **Formalization Note** A homogeneous polynomial vanishes at a projective point iff it vanishes at one (equivalently every) representative; the statement evaluates at Mathlib's representative `x.rep`. The bound $d=O\big((t|\tilde L_\beta|)^{1/3}\big)$ on the page is the arithmetic consequence of the binomial inequality and is not part of this statement. Holds over every field.
-- source:
--   Rudnev, On the number of incidences between points and planes in three dimensions, arXiv:1407.0426v5, pp. 15–16, §5, "There is a nonzero homogeneous polynomial of degree d … by the rank-nullity theorem"

import Mathlib
import Definitions.Def_RudnevIncidence_PointPlane_Setting

namespace RudnevIncidence.PointPlane

open Classical Projectivization
open scoped LinearAlgebra.Projectivization

theorem vanishing_polynomial {F : Type*} [Field F] (X : Finset (ℙ F (Fin 4 → F))) (d : ℕ)
    (hX : X.card < (d + 3).choose 3) :
    ∃ Q : MvPolynomial (Fin 4) F, Q ≠ 0 ∧ Q.IsHomogeneous d ∧
      ∀ x ∈ X, MvPolynomial.eval x.rep Q = 0 := by sorry
end RudnevIncidence.PointPlane
