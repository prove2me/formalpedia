-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_weighted_generalized_eigenspace_dimension
-- name    : WeierstrassEllipticZeta.weighted_generalized_eigenspace_dimension
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-10T15:39:27.722546+00:00
-- url     : https://prove2.me/theorems/2b1697a3-1c5a-4269-97df-ae1e8c1e77d3
-- title:
--   Weighted dimensions of generalized eigenspaces from a factored characteristic polynomial
-- statement:
--   Let $K$ be a field, $n\in\mathbb N$, and $V$ a finite type. Let
--   $A$ be an $n\times n$ matrix over $K$, let $w:V\to\mathbb N$,
--   and let $f:V\to K$. Suppose
--   $$
--   \chi_A(X)=\prod_{v\in V}(X-f(v))^{w(v)}.
--   $$
--   For $z\in K$, write
--   $$
--   E_z^{(N)}=\ker(A-zI_n)^N,\qquad
--   E_z^{(\infty)}=\bigcup_{j\ge0}\ker(A-zI_n)^j.
--   $$
--   Then
--   $$
--   \dim_K E_z^{(\infty)}=\sum_{\substack{v\in V\\f(v)=z}}w(v),
--   $$
--   and the same formula holds for $\dim_K E_z^{(N)}$ whenever $N\ge n$.
--   The values $f(v)$ need not be distinct; every index in the fibre
--   contributes its weight. Zero weights, empty index types and $n=0$
--   are allowed. No characteristic assumption on $K$ is required.
-- source:
--   Derived linear-algebra lemma for the approach associated with Senthil Kumar K (2026), Appendix A and Theorem A.2, https://doi.org/10.1017/S001309152610145X. This lemma is proved here and is not quoted from the article. If a matrix characteristic polynomial factors as a product of powers of X-f(v), its maximal generalized eigenspace at z has dimension equal to the sum of weights over f(v)=z. The same dimension holds at every generalized-eigenspace order at least the matrix size. Repeated values, zero weights and empty index types are allowed. Uses Mathlib root multiplicities and generalized-eigenspace stabilization. No Prove2Me theorem dependencies or new definitions.

import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.Algebra.Polynomial.Roots

open scoped Classical

theorem WeierstrassEllipticZeta.weighted_generalized_eigenspace_dimension
    (K : Type*) [Field K] (n : ℕ) (V : Type*) [Fintype V]
    (A : Matrix (Fin n) (Fin n) K) (w : V → ℕ) (f : V → K)
    (hchar : A.charpoly = ∏ v : V, (Polynomial.X - Polynomial.C (f v)) ^ w v) :
    ∀ z : K,
      Module.finrank K (Module.End.maxGenEigenspace A.mulVecLin z) =
        ∑ v ∈ Finset.univ.filter (fun v : V => f v = z), w v ∧
      ∀ N : ℕ, n ≤ N →
        Module.finrank K (Module.End.genEigenspace A.mulVecLin z N) =
          ∑ v ∈ Finset.univ.filter (fun v : V => f v = z), w v := by sorry
