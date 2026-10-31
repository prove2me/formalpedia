-- Prove2me | Theorems.Thm_SPQPoly_sos_cone_closed
-- name    : SPQPoly.sos_cone_closed
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:36:15.270137+00:00
-- url     : https://prove2.me/theorems/532f4db0-c90e-4e65-9ff8-d69f24b74689
-- title:
--   Theorem 3.4, proof (citing [33]) — the cone of sos polynomials of bounded degree is closed
-- statement:
--   Fix $n$ and $D$. Let $P_1,P_2,\dots$ be sums of squares of real polynomials in $n$ variables, each of total degree at most $D$, and suppose $P_k\to p$ coefficientwise: for every monomial $x^\alpha$ the coefficient of $x^\alpha$ in $P_k$ tends to the coefficient of $x^\alpha$ in $p$. Then $p$ is a sum of squares.
--
--   In other words, the sos cone $\Sigma_{n,\le D}$ is closed in the finite-dimensional space of polynomials of degree at most $D$. The proof of Theorem 3.4 uses it for $n=2$ to perturb the sextic of Theorem 3.2 into higher degrees.
--
--   **Formalization Note** Closedness is sequential closedness under coefficientwise convergence, which is closedness in the finite-dimensional coefficient space.
--
--   Differences from the source:
--   - reading: the cone Σ_{2,d} → sos polynomials of total degree at most D; reason: the set of sos polynomials of exact degree D is not closed (t·x₁^D → 0); the proof applies it to q_t, of degree at most d
--   - generalization: n = 2 → every number of variables n; reason: the n = 2 case is the specialization
--   - encoding: closedness of the cone → limits of coefficientwise convergent sequences of sos polynomials of degree ≤ D are sos; reason: in a finite-dimensional real space sequential closedness is closedness, and coefficientwise convergence is convergence
-- source:
--   Ahmadi, Dibek & Hall, Sums of Separable and Quadratic Polynomials, arXiv:2105.04766v1, Theorem 3.4, proof, p.13 (citing [33])

import Mathlib

open MvPolynomial Filter Topology

namespace SPQPoly

/-- **The cone of sos polynomials of bounded degree is closed.**
Ahmadi, Dibek & Hall, *Sums of Separable and Quadratic Polynomials*, arXiv:2105.04766v1, Theorem 3.4, proof, p.13 (citing [33]): "Suppose for the sake of contradiction that qt(x) was
sos for every t > 0. Then, by the closedness of the cone Σ2,d (see [33]), the polynomial q0(x)
must be sos, which is a contradiction."

If a sequence `P k` of sos polynomials in `n` variables, all of total degree at most `D`,
converges coefficientwise to `p`, then `p` is sos.

**Formalization Note.** Closedness is sequential closedness in the coefficient space of the
polynomials of total degree `≤ D` (a finite-dimensional real space, where sequential closedness is
closedness and coefficientwise convergence is convergence). The degree bound is essential: the
set of exact degree `D` is not closed (`t·x₁^D → 0`). Stated for every `n` (the paper uses
`n = 2`). -/
theorem sos_cone_closed {n D : ℕ} (P : ℕ → MvPolynomial (Fin n) ℝ) (p : MvPolynomial (Fin n) ℝ)
    (hdeg : ∀ k, (P k).totalDegree ≤ D) (hsos : ∀ k, IsSumSq (P k))
    (hlim : ∀ m : Fin n →₀ ℕ, Tendsto (fun k => (P k).coeff m) atTop (𝓝 (p.coeff m))) :
    IsSumSq p := by sorry

end SPQPoly
