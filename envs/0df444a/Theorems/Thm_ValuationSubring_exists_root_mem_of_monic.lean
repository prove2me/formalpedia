-- Prove2me | Theorems.Thm_ValuationSubring_exists_root_mem_of_monic
-- name    : ValuationSubring.exists_root_mem_of_monic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/6e53b709-8d12-5e06-8b9c-0d341e70cd7d
-- title:
--   Monic polynomials over a valuation subring of an algebraically closed field have roots in it
-- statement:
--   Let $K$ be a field that is algebraically closed, and let $A$ be a valuation subring of $K$. Let $f$ be a polynomial with coefficients in $A$, assumed monic and with $\mathrm{natDegree}\, f \neq 0$. The assertion is that there exists an element $x$ of $A$ such that the image of $f$ under the evaluation map $\mathrm{aeval}$ at the image of $x$ in $K$ vanishes; that is, $f$ has a root lying in $A$, the root being exhibited as an element of $A$ whose image in $K$ annihilates $f$ under the $A$-algebra structure of $K$. Note that the degree hypothesis is phrased via the natural-number degree being nonzero, which for a monic (hence nonzero) polynomial is the same as positive degree.
--
--   This is the standard root-lifting observation that a valuation ring is integrally closed in its field of fractions, combined with algebraic closedness of that field. It is used to prove that the residue field of a valuation subring of an algebraically closed field is again algebraically closed ([`ValuationSubring.isAlgClosed_residueField`](thm.html#ValuationSubring.isAlgClosed_residueField)), and thence in the construction of points of Weierstrass curves over such rings reducing to prescribed points ([`WeierstrassCurve.exists_mem_rationalHomSet_reduceHom_comp_eq_comp_reduceHom`](thm.html#WeierstrassCurve.exists_mem_rationalHomSet_reduceHom_comp_eq_comp_reduceHom)).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_exists_root_mem_of_monic.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ValuationSubring.exists_root_mem_of_monic {K : Type*} [Field K] [IsAlgClosed K]
    (A : ValuationSubring K) (f : Polynomial A) (hf : f.Monic) (hd : f.natDegree ≠ 0) :
    ∃ x : A, Polynomial.aeval (x : K) f = 0 := by sorry
