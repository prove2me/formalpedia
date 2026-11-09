-- Prove2me | Theorems.Thm_UnaryParityLifting_Exact_averaged_certificate
-- name    : UnaryParityLifting.Exact.averaged_certificate
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:10:00.951626+00:00
-- url     : https://prove2.me/theorems/4784204e-bc43-4909-b9f5-7b78ff44ca8a
-- title:
--   Lemma 4.1 — Averaged certificate
-- statement:
--   Let $N,S\ge1$, let $g$ be a surjective 1-stifling gadget, and let $F$ be a width-at-most-$w$ source CNF with no empty clause. Suppose $F\circ g$ has an integer parity certificate of charged size at most $S$. Put $T=(mN+2)S$. For every $1\le R\le N$, there are nonnegative constants $\beta_C$, a conical function $J$, and a real error $E$ satisfying
--   $$P:=\sum_{C\in F}\beta_C\overline C=1+J+E.$$
--   All of the following hold:
--   1. $\sum_C\beta_C\le S$ and at most $S$ axiom coefficients are nonzero.
--   2. $J$ has a conical representation of degree at most $R$, mass at most $T2^R$, and $0\le J(z)\le T$ for every $z$.
--   3. $E(z)\ge0$ for every $z$ and $\|E\|_1\le T2^{-c_gR}$.
--   4. If $w\le R$, the total function $E$ has multilinear polynomial degree at most $R$; if $R=N$, then $E=0$ exactly.
--
--   The polynomial degree clause concerns the total error. The statement starts from the original parity certificate, without an assumed normalized identity or any assumed affine decomposition.
--
--   Differences from the source:
--   - encoding: coordinates indexed by [N] and [m], bits in {0,1} → Fin N and Fin m, Bool bits with false = 0 and true = 1; reason: zero-based labels and the explicit bit maps preserve every assignment
--   - encoding: written monomials and clause occurrences plus unary coefficient mass → collected integer MvPolynomial monomials, positive explicit encoding charges and a list of weighted parity clauses; reason: the source fixes no binary serialization; all written occurrences and unary coefficients are charged, and arbitrary exponents remain allowed
--   - generalization: a certificate of size S → a certificate of charged size at most S; reason: the proof uses only upper bounds by S and the exactly-sized source certificate is included
--   - encoding: surjective gadget convention of Definition 2.5, retained throughout Sections 3–4 → an explicit Function.Surjective g hypothesis; reason: excludes empty gadget fibers and the zero-bit vacuity of the reused stifling predicate without excluding any source gadget
--   - encoding: nonnegative finite sums of conjunctions, identical terms collected → one NNReal coefficient for each distinct Option Bool term; reason: the finite term type includes every consistent conjunction, including the empty term, and degree constrains nonzero terms before cancellation
--   - encoding: Walsh norm with chi_U(z) = (-1) to the sum of the bits in U → FourierEntropyApprox.spectralNorm on Bool assignments, with true giving Walsh sign -1; reason: the referenced code has exactly the same uniform normalization, characters and empty Fourier set
--   - encoding: P is defined to be the axiom sum; E has multilinear degree at most R when w <= R → P is the displayed sum directly, and the degree clause asserts existence of a multilinear representative of E; reason: P is not an independent parameter and the representative defines precisely the polynomial degree of this cube function
-- source:
--   Yaroslav Alekseev, Lifting to Unary Sherali–Adams over Parities, STOC 2027 submission #567 (October 2026), citation_basis: published; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/567.pdf; pp.13–14, Lemma 4.1, equation (4.1), and Section 4 standing assumptions

import Mathlib
import Definitions.Def_UnaryParityLifting_Exact_averaging
import Definitions.Def_UnaryParityLifting_Exact_conicalRepresentations
import Definitions.Def_FourierEntropyApprox_fourierCoeff

namespace UnaryParityLifting.Exact

open scoped BigOperators

/-- Alekseev, STOC 2027 submission #567 (October 2026), pp.13–14, Lemma 4.1.
N ≥ 1 and S ≥ 1 are the Section 4 preamble; only this result excludes empty clauses. -/
theorem averaged_certificate (m N w S R : ℕ) (g : (Fin m → Bool) → Bool)
    (hg : Function.Surjective g) (hstifling : LiftSAParity.IsOneStifling g)
    (hN : 1 ≤ N) (hS : 1 ≤ S) (F : LiftSAParity.CNF (Fin N))
    (hF : WidthAtMost F w) (hempty : ∀ C ∈ F, C.Nonempty)
    (hR : 1 ≤ R) (hRN : R ≤ N) (enc : EncodingCharge (Fin N × Fin m))
    (hcert : HasParityCertificate (LiftSAParity.lift F g) enc S) :
    ∃ (β : {C // C ∈ F} → NNReal) (J : ConicalRepresentation (Fin N))
      (E : (Fin N → Bool) → ℝ),
      (∀ z, (∑ C : {C // C ∈ F}, (β C : ℝ) * clauseIndicator C.val z) =
        1 + J.value z + E z) ∧
      (∑ C : {C // C ∈ F}, (β C : ℝ)) ≤ (S : ℝ) ∧
      (Finset.univ.filter (fun C => β C ≠ 0)).card ≤ S ∧
      J.DegreeLE R ∧ J.mass ≤ (normalizationBudget m N S : ℝ) * (2 : ℝ) ^ R ∧
      (∀ z, 0 ≤ J.value z ∧ J.value z ≤ (normalizationBudget m N S : ℝ)) ∧
      (∀ z, 0 ≤ E z) ∧
      FourierEntropyApprox.spectralNorm E ≤ (normalizationBudget m N S : ℝ) * errorBound g R ∧
      (w ≤ R → MultilinearDegreeLE E R) ∧ (R = N → E = 0) := by sorry

end UnaryParityLifting.Exact
