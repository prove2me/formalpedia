-- Prove2me | Theorems.Thm_PSDPolyApprox_slack_submatrix_factorization
-- name    : PSDPolyApprox.slack_submatrix_factorization
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:52:02.229496+00:00
-- url     : https://prove2.me/theorems/b936fe8f-c844-44d2-a0b1-11650e3d34dc
-- title:
--   §3, pp.4–5 — the matrix (4) has a nonnegative factorization of size $\operatorname{xc}(Q)$ (corrected: $n\ge2$)
-- statement:
--   Let $n\ge2$, $0<\epsilon<1$, and let $Q$ be a polytope with
--   $$
--   (1-\epsilon)\Bigl(\mathcal D-\tfrac1nI_n\Bigr)\subseteq Q\subseteq\mathcal D-\tfrac1nI_n .
--   $$
--   Then the $2^n\times2^n$ matrix (4),
--   $$
--   M_\epsilon(x,y)=(1-\epsilon)\frac1n(x^{\mathsf T}y)^2+\epsilon\qquad(x,y\in\{-1,1\}^n),
--   $$
--   can be written as a sum of $\operatorname{xc}(Q)$ entrywise nonnegative rank-one matrices; that is, $\operatorname{rank}_+(M_\epsilon)\le\operatorname{xc}(Q)$.
--
--   This is the step of the proof that turns a small polytope between $(1-\epsilon)C$ and $C$, $C=\mathcal D-\frac1nI_n$, into a small nonnegative factorization: the rows of $M_\epsilon$ are the points $(1-\epsilon)(\frac1nxx^{\mathsf T}-\frac1nI_n)$ of $(1-\epsilon)C$, the columns are the valid inequalities $\langle I_n-yy^{\mathsf T},X\rangle\le1$ of $C$, and the entries are the slacks.
--
--   Differences from the source:
--   - correction: the hypercube submatrix (4) of the slack matrix of ((1 − ǫ)C, C) has nonnegative rank at most xc(Q), for every n → the same for n ≥ 2; reason: at n = 1, C = {0}, so Q = {0} has xc(Q) = 0, while (4) is the nonzero all-ones 2 × 2 matrix
--   - reading: "we are thus led to study the nonnegative rank of" (3) and its submatrix (4), via Theorem 4 → an explicit statement that (4) has a nonnegative factorization of size xc(Q); reason: this is the inequality the text uses; it is stated separately because C is not full-dimensional in ℝ^{n×n}, so Theorem 4 does not apply verbatim
--   - encoding: rows and columns indexed by {−1/√n, +1/√n}^n → rows and columns indexed by {−1, 1}^n with the entry (1 − ǫ)(1/n)(xᵀy)² + ǫ; reason: the paper's own rescaling in (4)
--   - encoding: sets of n × n matrices → their images in ℝ^{n×n} under the flattening Matrix.vec; reason: vec is a linear isomorphism carrying the trace inner product to the dot product; extension complexity is invariant under it (equations are free)
--   - encoding: extension complexity = smallest number of facets of a polytope whose linear image is P (Definition 1) → smallest number of inequalities of an extended formulation of P (ExtensionComplexity.TSP.extensionComplexity); reason: the two minima coincide for polytopes of dimension ≥ 1 (Fiorini et al., J. ACM 2015, Theorem 3, published as ExtensionComplexity.TSP.yannakakis_factorization), and every polytope in this statement has dimension ≥ 1
-- source:
--   Fawzi, On polyhedral approximations of the positive semidefinite cone, arXiv:1811.09649v1, §3, pp.4–5, the slack-matrix computation and equation (4)

import Mathlib
import Definitions.Def_ExtensionComplexity_TSP_Polytope
import Definitions.Def_ExtensionComplexity_TSP_extensionComplexity
import Definitions.Def_ExtensionComplexity_TSP_SlackMatrix
import Definitions.Def_PSDPolyApprox_shiftedDensity
import Definitions.Def_PSDPolyApprox_slackSubmatrix

open ExtensionComplexity.TSP
open scoped Pointwise

namespace PSDPolyApprox

/-- **The matrix (4) has a nonnegative factorization of size `xc(Q)`.**
Fawzi, arXiv:1811.09649v1, §3, pp.4–5: "By checking that
1 − ⟨(1 − ǫ)(xxT − 1/n In), In − nyyT⟩ = (1 − ǫ)n(xT y)2 + ǫ we are thus led to study the
nonnegative rank of the following inﬁnite matrix … It will be enough for us to consider the
submatrix indexed by elements of the hypercube {−1/√n, +1/√n}n" — the matrix (4).

For `n ≥ 2`, `0 < ε < 1` and a polytope `Q` with `(1 − ε)(D − (1/n)Iₙ) ⊆ Q ⊆ D − (1/n)Iₙ`, the
`2ⁿ × 2ⁿ` matrix `(x, y) ↦ (1 − ε)(1/n)(xᵀy)² + ε` has a nonnegative factorization with
`xc(Q)` rank-one terms, i.e. `rank₊ ≤ xc(Q)`.

**Formalization Note.** This is the "rank₊ ≤ xc" half of Theorem 4 for the pair
`((1 − ε)C, C)`, `C = D − (1/n)Iₙ`, restricted to the hypercube rows and columns; it is a separate
statement because `C` is not full-dimensional in `ℝ^{n×n}`. `n ≥ 2` is needed: at `n = 1`,
`Q = {0}` has `xc = 0` while the matrix is the nonzero all-ones `2 × 2` matrix. -/
theorem slack_submatrix_factorization (n : ℕ) (hn : 2 ≤ n) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (Q : Set (Fin n × Fin n → ℝ)) (hQ : IsPolytope Q)
    (hin : (1 - ε) • shiftedDensity n ((n : ℝ)⁻¹ • (1 : Matrix (Fin n) (Fin n) ℝ)) ⊆ Q)
    (hout : Q ⊆ shiftedDensity n ((n : ℝ)⁻¹ • (1 : Matrix (Fin n) (Fin n) ℝ))) :
    HasNonnegFactorization (slackSubmatrix ε n) (extensionComplexity Q) := by sorry

end PSDPolyApprox
