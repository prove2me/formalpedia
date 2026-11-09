-- Prove2me | Theorems.Thm_UnaryParityLifting_Exact_exact_coefficient_lifting
-- name    : UnaryParityLifting.Exact.exact_coefficient_lifting
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:09:50.589197+00:00
-- url     : https://prove2.me/theorems/5433873a-5747-4631-8cb8-3b38fbe862d8
-- title:
--   Theorem 4.3 — Exact coefficient lifting
-- statement:
--   Fix any surjective 1-stifling gadget $g:\{0,1\}^m\to\{0,1\}$ and define $M_g=\max_b|g^{-1}(b)|$, $\delta_g=2/(mM_g)$ and $c_g=-\log_2(1-\delta_g/2)$. Let $N,S\ge1$, and let $F$ be a width-at-most-$w$ CNF on $N$ variables, where $w\ge1$ and clauses have no complementary pair. Empty clauses are allowed. Suppose $F\circ g$ has an integer uSA(⊕) certificate of charged size at most $S$. Put $T=(mN+2)S$. If
--   $$w\le R\le N,\qquad T2^{-c_gR}\le\tfrac12,$$
--   then there is an exact real Sherali–Adams certificate
--   $$\sum_{C\in F}a_C\overline C=1+\sum_t\lambda_t t,\qquad a_C,\lambda_t\ge0,$$
--   with all three quantitative conclusions:
--   $$\deg\le R,\qquad\sum_Ca_C+\sum_t\lambda_t\le6T2^R,\qquad|\{C:a_C\ne0\}|\le S.$$
--
--   The axiom multipliers $a_C$ are constants; degree is measured before cancellation and every used conical term has degree at most $R$. Equality is formal equality of multilinear real polynomials with no Boolean-axiom multipliers. All certificate data in the conclusion are constructed existentially from the original input certificate. This is the full technical form of the paper's headline Theorem 1.1, including axiom support.
--
--   Differences from the source:
--   - encoding: coordinates indexed by [N] and [m], bits in {0,1} → Fin N and Fin m, Bool bits with false = 0 and true = 1; reason: zero-based labels and the explicit bit maps preserve every assignment
--   - encoding: written monomials and clause occurrences plus unary coefficient mass → collected integer MvPolynomial monomials, positive explicit encoding charges and a list of weighted parity clauses; reason: the source fixes no binary serialization; all written occurrences and unary coefficients are charged, and arbitrary exponents remain allowed
--   - generalization: a certificate of size S → a certificate of charged size at most S; reason: the proof uses only upper bounds by S and the exactly-sized source certificate is included
--   - encoding: surjective gadget convention of Definition 2.5, retained throughout Sections 3–4 → an explicit Function.Surjective g hypothesis; reason: excludes empty gadget fibers and the zero-bit vacuity of the reused stifling predicate without excluding any source gadget
--   - encoding: nonnegative finite sums of conjunctions, identical terms collected → one NNReal coefficient for each distinct Option Bool term; reason: the finite term type includes every consistent conjunction, including the empty term, and degree constrains nonzero terms before cancellation
--   - encoding: exact equality of multilinear real polynomials with constant nonnegative axiom multipliers → RealCertificate.IsExact in MvPolynomial, with NNReal axiom and conical coefficients; reason: the source proof establishes this formal identity on p.15 with no Boolean-axiom multipliers
-- source:
--   Yaroslav Alekseev, Lifting to Unary Sherali–Adams over Parities, STOC 2027 submission #567 (October 2026), citation_basis: published; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/567.pdf; pp.14–15, Theorem 4.3, equations (4.3)–(4.5); p.9, equation (3.3); p.13, Section 4 standing assumptions

import Mathlib
import Definitions.Def_UnaryParityLifting_Exact_averaging
import Definitions.Def_UnaryParityLifting_Exact_conicalRepresentations

namespace UnaryParityLifting.Exact

/-- Alekseev, STOC 2027 submission #567 (October 2026), pp.14–15, Theorem 4.3.
Complete explicit degree, mass and axiom-support conclusion. Empty clauses are allowed. -/
theorem exact_coefficient_lifting (m N w S R : ℕ) (g : (Fin m → Bool) → Bool)
    (hg : Function.Surjective g) (hstifling : LiftSAParity.IsOneStifling g)
    (hN : 1 ≤ N) (hS : 1 ≤ S) (F : LiftSAParity.CNF (Fin N))
    (hF : WidthAtMost F w) (enc : EncodingCharge (Fin N × Fin m))
    (hcert : HasParityCertificate (LiftSAParity.lift F g) enc S)
    (hwR : w ≤ R) (hRN : R ≤ N)
    (hsmall : (normalizationBudget m N S : ℝ) * errorBound g R ≤ 1 / 2) :
    ∃ q : RealCertificate F,
      q.IsExact ∧ q.DegreeLE R ∧
      q.mass ≤ 6 * (normalizationBudget m N S : ℝ) * (2 : ℝ) ^ R ∧
      q.axiomSupport ≤ S := by sorry

end UnaryParityLifting.Exact
