-- Prove2me | Theorems.Thm_QuasiStrictNE_theorem_3
-- name    : QuasiStrictNE.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T13:10:35.271952+00:00
-- url     : https://prove2.me/theorems/c6385f84-5e7f-442b-8209-19d8399d8bd5
-- title:
--   Theorem 3 (Etessami–Yannakakis) — exact rational fixed points: polynomial size and PPAD membership
-- statement:
--   For every polynomial piecewise-linear fixed-point problem (Definition 6):
--
--   1. every instance $I$ has a rational fixed point $x\in D_I$, $F_I(x)=x$, whose encoding length is polynomial in $|I|$ (one polynomial for all instances);
--   2. the search problem of computing an exact rational fixed point belongs to PPAD.
--
--   The paper cites this from [EY10, Theorem 5.2].
--
--   Differences from the source:
--   - reading: the search problem of computing such an exact rational fixed point → FixSearch: every exact rational fixed point in D_I is an answer; the polynomial length bound is clause 1; reason: 'such' refers to an exact rational fixed point; the length bound is stated as the existence clause; nothing is lost, since the polynomial-time answer map of a reduction to End-of-Line outputs codes of length polynomial in |I|
--   - reading: PPAD = total search problems reducible to End-of-Line, End-of-Line described in words (p.8) → PPAD = {Q | Q total ∧ Q ≤ₚ EndOfLine}, End-of-Line in the circuit form P(0ⁿ) = 0ⁿ ≠ S(0ⁿ), answers x with P(S(x)) ≠ x or S(P(x)) ≠ x ≠ 0ⁿ; reason: the standard Daskalakis–Goldberg–Papadimitriou formalization of the paper's verbal definition; reductions are the paper's p.8 search reductions
--   - reading: a collection of hyperplanes dividing DI into polyhedral regions on each of which FI is affine, coefficients of encoding length polynomial in |I| uniformly → a finite set of rational hyperplanes (a pair with a = 0 is allowed and cuts nothing); on every closed sign cell intersected with the domain a rational affine formula; every coefficient of encoding length ≤ q(|I|) for one polynomial q; reason: the paper's own regions R_T are closed (p.16, 'including its boundary'); the number of hyperplanes is not bounded (p.16 uses one per subset T)
--   - encoding: a polynomial-time algorithm interacting with a linear-comparison oracle → one step function, PolyTimeComputable on (instance, answers so far), run for q(|I|) rounds; queries coded by encRatVec/encRat, malformed queries answered false; output No = [false, false], or the tagged code of (C, c); reason: a model of the paper's oracle algorithms; every step and the whole run are polynomial in |I|
--   - encoding: DI a nonempty compact convex polytope given by linear inequalities computable from I in polynomial time → PLFPData with ineqs; D_I nonempty and bounded; a PolyTimeComputable map outputs dim I and the inequalities (encBin, encRatVec, encRat); reason: a set given by finitely many inequalities is closed and convex, so nonempty + bounded is nonempty compact convex
-- source:
--   Hansen & Nie, On Existence and Computational Complexity of Quasi-strict Equilibria, arXiv:2611.06350 (preprint, sha256 c265dace…), Theorem 3, p.9 ([EY10, Theorem 5.2])

import Mathlib
import Definitions.Def_CardinalMatching_encRatMatrix
import Definitions.Def_QuasiStrictNE_PLFPData
import Definitions.Def_QuasiStrictNE_PLFPData_D
import Definitions.Def_QuasiStrictNE_IsPLFP
import Definitions.Def_QuasiStrictNE_FixSearch
import Definitions.Def_QuasiStrictNE_PPAD

namespace QuasiStrictNE

/-- **Theorem 3 (Etessami–Yannakakis)** (Hansen & Nie, *On Existence and Computational Complexity of
Quasi-strict Equilibria*, arXiv:2611.06350, Theorem 3, p.9: "For every instance I of a polynomial
piecewise-linear fixed-point problem, there exists a rational fixed point x s.t. FI(x) = x and its
encoding length is polynomial in |I|. The search problem of computing such an exact rational fixed
point belongs to PPAD"; cited from [EY10, Theorem 5.2]).

For every polynomial piecewise-linear fixed-point problem `Φ` (Definition 6):

1. there is a polynomial `q` such that every valid instance `I` has a rational point `x ∈ D_I` with
   `F_I(x) = x` whose code has length at most `q(|I|)`;
2. the search problem `FixSearch Φ` (find an exact rational fixed point) belongs to PPAD.

**Formalization Note** The answers of `FixSearch Φ` are all exact rational fixed points; the length
bound is clause 1. PPAD is the paper's class (p.8): total and reducible to End-of-Line. -/
theorem theorem_3 (Φ : PLFPData) (hΦ : IsPLFP Φ) :
    (∃ q : Polynomial ℕ, ∀ I, Φ.valid I → ∃ x : Fin (Φ.dim I) → ℚ,
      (fun i => (x i : ℝ)) ∈ Φ.D I ∧ Φ.F I (fun i => (x i : ℝ)) = (fun i => (x i : ℝ)) ∧
      (CardinalMatching.encRatVec (Φ.dim I) x).length ≤ q.eval I.length) ∧
    FixSearch Φ ∈ PPAD := by sorry

end QuasiStrictNE
