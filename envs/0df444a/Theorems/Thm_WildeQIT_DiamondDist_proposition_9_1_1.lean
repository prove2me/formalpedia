-- Prove2me | Theorems.Thm_WildeQIT_DiamondDist_proposition_9_1_1
-- name    : WildeQIT.DiamondDist.proposition_9_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:19:57.765961+00:00
-- url     : https://prove2.me/theorems/59698268-48fe-487b-9871-85fe337cc832
-- title:
--   Proposition 9.1.1: $\|M\|_1$ equals the sum of the singular values of $M$
-- statement:
--   Let $M\in\mathcal L(\mathcal H,\mathcal H')$ be an operator between finite-dimensional complex Hilbert spaces, and let $\sigma_0(M)\ge\sigma_1(M)\ge\cdots\ge0$ be its singular values: the square roots of the eigenvalues of $M^\dagger M$, listed with multiplicity in non-increasing order. The trace norm $\|M\|_1=\operatorname{Tr}\{|M|\}$, $|M|=\sqrt{M^\dagger M}$, is equal to the sum of the singular values:
--
--   $$
--   \|M\|_1=\sum_i \sigma_i(M).
--   $$
--
--   This identifies the trace norm with the Schatten 1-norm and is the basis for the norm properties and the isometric invariance of the trace norm.
--
--   **Formalization Note** $M$ is a complex matrix over finite index types; `WildeQIT.traceNorm M` is the real part of the trace of `CFC.sqrt (Mᴴ * M)`. The singular values are Mathlib's `LinearMap.singularValues` of the linear map $z\mapsto Mz$ from $\mathbb C^n$ to $\mathbb C^m$ (`Matrix.toEuclideanLin M`), a finitely supported sequence indexed by $\mathbb N$ whose first $\dim\mathcal H$ entries are $\sqrt{\lambda_i(M^\dagger M)}$ and whose remaining entries are $0$; the sum is the `Finsupp.sum` of this sequence.
--
--   Differences from the source:
--   - encoding: operator $M\in\mathcal L(\mathcal H,\mathcal H')$ → matrix `M : Matrix m n ℂ` over finite index types; reason: the book works in finite dimensions, standard bases
--   - encoding: the strictly positive singular values $\sigma_0,\dots,\sigma_{d-1}$, $d=\operatorname{rank}M$ (9.3) → Mathlib's `(Matrix.toEuclideanLin M).singularValues`, which also lists zeros; reason: zero singular values add nothing to the sum
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Proposition 9.1.1, p. 250

import Definitions.Def_WildeQIT_traceNorm
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Proposition 9.1.1, p. 250.
-/

namespace WildeQIT.DiamondDist

/-- **Proposition 9.1.1** (Wilde, arXiv:1106.1445v8, p. 250). The trace norm of an operator
`M ∈ L(H, H′)` is equal to the sum of its singular values.

Formalization Note: `M : Matrix m n ℂ` over finite index types (finite-dimensional spaces).
The singular values are Mathlib's `LinearMap.singularValues` of the linear map
`Matrix.toEuclideanLin M : EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ m`, a finitely supported
sequence `ℕ →₀ ℝ` (the square roots of the eigenvalues of `M†M` in non-increasing order, then
zeros); the sum of the singular values is the `Finsupp.sum` of that sequence. -/
theorem proposition_9_1_1 {m n : Type} [Fintype m] [Fintype n] [DecidableEq n]
    (M : Matrix m n ℂ) :
    traceNorm M = (Matrix.toEuclideanLin M).singularValues.sum (fun _ σ => σ) := by sorry

end WildeQIT.DiamondDist
