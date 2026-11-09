-- Prove2me | Theorems.Thm_UnaryParityLifting_Exact_fourier_repair
-- name    : UnaryParityLifting.Exact.fourier_repair
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:09:35.504389+00:00
-- url     : https://prove2.me/theorems/80a2f99d-7601-4238-af90-d52c8e520c72
-- title:
--   Lemma 4.2 — Fourier repair
-- statement:
--   Let $1\le R\le N$ and let $E$ be any real multilinear polynomial on $N$ Boolean variables of total degree at most $R$. Set $K=\|E\|_1$, where the norm is taken after evaluating $E$ on the cube and expanding in the uniformly normalized Walsh basis. There is a conical representation $B$ such that, as real polynomials,
--   $$B=E+K,\qquad\deg_{\mathrm{conical}}B\le R,\qquad\sum_t\lambda_t\le2^R K.$$
--
--   No nonnegativity assumption is made on $E$. The constant Fourier character is included; in particular constant polynomials and the zero polynomial are covered. This result turns control of the total Fourier error into an exact conical certificate with the stated mass and degree bounds.
--
--   Differences from the source:
--   - encoding: coordinates indexed by [N] and [m], bits in {0,1} → Fin N and Fin m, Bool bits with false = 0 and true = 1; reason: zero-based labels and the explicit bit maps preserve every assignment
--   - encoding: nonnegative finite sums of conjunctions, identical terms collected → one NNReal coefficient for each distinct Option Bool term; reason: the finite term type includes every consistent conjunction, including the empty term, and degree constrains nonzero terms before cancellation
--   - encoding: Walsh norm with chi_U(z) = (-1) to the sum of the bits in U → FourierEntropyApprox.spectralNorm on Bool assignments, with true giving Walsh sign -1; reason: the referenced code has exactly the same uniform normalization, characters and empty Fourier set
-- source:
--   Yaroslav Alekseev, Lifting to Unary Sherali–Adams over Parities, STOC 2027 submission #567 (October 2026), citation_basis: published; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/567.pdf; p.14, Lemma 4.2, equation (4.2)

import Mathlib
import Definitions.Def_UnaryParityLifting_Exact_conicalRepresentations
import Definitions.Def_FourierEntropyApprox_fourierCoeff

namespace UnaryParityLifting.Exact

/-- Alekseev, STOC 2027 submission #567 (October 2026), p.14, Lemma 4.2.
E may have either sign. The empty Fourier set is included in the norm. -/
theorem fourier_repair (N R : ℕ) (hR : 1 ≤ R) (hRN : R ≤ N)
    (E : MvPolynomial (Fin N) ℝ) (hE : Multilinear E) (hdeg : E.totalDegree ≤ R) :
    let K := FourierEntropyApprox.spectralNorm (fun z : Fin N → Bool => MvPolynomial.eval (fun i => realBit (z i)) E)
    ∃ J : ConicalRepresentation (Fin N),
      J.DegreeLE R ∧ J.mass ≤ (2 : ℝ) ^ R * K ∧
      J.polynomial = E + MvPolynomial.C K := by sorry

end UnaryParityLifting.Exact
