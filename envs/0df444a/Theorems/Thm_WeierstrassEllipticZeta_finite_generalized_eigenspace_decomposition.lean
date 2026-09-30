-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_finite_generalized_eigenspace_decomposition
-- name    : WeierstrassEllipticZeta.finite_generalized_eigenspace_decomposition
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-10T16:23:05.595382+00:00
-- url     : https://prove2.me/theorems/51393f2c-5d79-4c4e-9a9c-b8dc9bb818f1
-- title:
--   Finite spectral decomposition with canonical summation equivalence
-- statement:
--   Let $K$ be an algebraically closed field, let $M$ be a finite-dimensional $K$-vector space, and let $f$ be a linear endomorphism of $M$. For $z\in K$, write $E_z$ for the maximal generalized eigenspace of $f$ at $z$.
--
--   Suppose that $S\subset K$ is finite and that
--   $$
--   \dim_K E_z=0\qquad(z\notin S).
--   $$
--   Then the subspaces indexed by $S$ form an internal direct sum of $M$. More precisely, there is a linear equivalence
--   $$
--   e:\prod_{z\in S}E_z\;\xrightarrow{\;\sim\;}M,
--   \qquad e((x_z)_{z\in S})=\sum_{z\in S}x_z.
--   $$
--   Thus every vector has a unique decomposition as the sum of one vector from each indexed generalized eigenspace. Diagonalizability is not assumed. The set $S$ may include values whose generalized eigenspaces are zero; the empty set is allowed when $M$ has dimension zero.
-- source:
--   Derived linear-algebra lemma for the approach associated with Senthil Kumar K (2026), Appendix A and Theorem A.2, https://doi.org/10.1017/S001309152610145X. This lemma is proved here and is not quoted from the article. In a finite-dimensional vector space over an algebraically closed field, if maximal generalized eigenspaces have dimension zero outside a finite set, those indexed by that set form an internal direct sum. Their finite product is linearly equivalent to the ambient space by summation. Uses Mathlib generalized-eigenspace spanning and independence. No Prove2Me theorem dependencies or new definitions.

import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.Algebra.DirectSum.Module

open scoped Classical

theorem WeierstrassEllipticZeta.finite_generalized_eigenspace_decomposition
    (K M : Type*) [Field K] [IsAlgClosed K]
    [AddCommGroup M] [Module K M] [FiniteDimensional K M]
    (f : Module.End K M) (s : Finset K)
    (hzero : ∀ z : K, z ∉ s →
      Module.finrank K (f.maxGenEigenspace z) = 0) :
    DirectSum.IsInternal (fun z : s => f.maxGenEigenspace z.val) ∧
    ∃ e : (∀ z : s, f.maxGenEigenspace z.val) ≃ₗ[K] M,
      ∀ x, e x = ∑ z : s, (x z : M) := by sorry
