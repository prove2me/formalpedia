-- Prove2me | Theorems.Thm_Polynomial_exists_isRoot_and_valuation_lt_one
-- name    : Polynomial.exists_isRoot_and_valuation_lt_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/a3d463fb-1b7c-52dc-95c8-879a04553525
-- title:
--   A root of valuation less than one from the Newton polygon
-- statement:
--   Let $K$ be an algebraically closed field and let $A \subseteq K$ be a valuation subring, with `A.valuation` the associated multiplicatively written valuation on $K$ taking values in the value group with zero attached to $A$, so that $A$ is the set of elements of valuation at most $1$. Let $f \in K[X]$ be a polynomial whose constant coefficient satisfies $A.\mathrm{valuation}(f_0) < 1$, and suppose that some coefficient is a unit for this valuation: there is an index $n \in \mathbb{N}$ with $A.\mathrm{valuation}(f_n) = 1$. The conclusion is that $f$ has a root $r \in K$ with $A.\mathrm{valuation}(r) < 1$, i.e. a root lying in the maximal ideal of $A$. No integrality hypothesis on the coefficients of $f$ is imposed, and $f \neq 0$ is not assumed separately (it follows from the hypothesis on $f_n$); for $n = 0$ the hypotheses are contradictory and the statement is vacuous.
--
--   This is the extreme segment of the Newton polygon of $f$ on the side of the constant term, in the form needed over a valuation subring of an algebraically closed field: a non-unit constant term together with a unit coefficient forces a root of valuation $< 1$. It is used in [`WeierstrassCurve.exists_torsionBy_residueChar_not_inZeroComponentAt`](thm.html#WeierstrassCurve.exists_torsionBy_residueChar_not_inZeroComponentAt), to produce a torsion point of an elliptic curve that does not reduce into the identity component at a place of multiplicative reduction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Polynomial_exists_isRoot_and_valuation_lt_one.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open Polynomial

theorem Polynomial.exists_isRoot_and_valuation_lt_one {K : Type*} [Field K] [IsAlgClosed K] (A : ValuationSubring K) {f : Polynomial K} (h0 : A.valuation (f.coeff 0) < 1) {n : ℕ} (hn : A.valuation (f.coeff n) = 1) : ∃ r : K, f.IsRoot r ∧ A.valuation r < 1 := by sorry
