-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_finite_summation_projector_resolution
-- name    : WeierstrassEllipticZeta.finite_summation_projector_resolution
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-10T16:57:28.972462+00:00
-- url     : https://prove2.me/theorems/f3ea3873-d46e-4914-b31c-e1c9f20831ee
-- title:
--   Canonical projections for a finite summation decomposition
-- statement:
--   Let $R$ be a commutative ring, $M$ an $R$-module, and $(E_i)_{i\in I}$ a finite family of submodules. Suppose that a linear equivalence
--   $$
--   e:\prod_{i\in I}E_i\xrightarrow{\;\sim\;}M
--   $$
--   is given by summation of the components. Then there are $R$-linear endomorphisms $P_i$ such that
--   $$
--   P_i(x)=(e^{-1}x)_i,\qquad
--   P_i^2=P_i,\qquad
--   P_iP_j=0\quad(i\ne j),\qquad
--   \sum_{i\in I}P_i=\operatorname{id}_M,
--   $$
--   where each component is viewed as an element of $M$. Their ranges are precisely the given submodules:
--   $$
--   \operatorname{range}P_i=E_i.
--   $$
--   Moreover, every $R$-linear endomorphism $g$ preserving all the submodules commutes with all the projectors:
--   $$
--   g(E_i)\subseteq E_i\quad\text{for all }i
--   \quad\Longrightarrow\quad
--   P_i g=gP_i\quad\text{for all }i.
--   $$
--   No field, finite-dimensionality or nonempty-index assumption is required. Pairwise zero products express algebraic orthogonality; no inner product is involved.
-- source:
--   Derived module-theoretic lemma for the approach associated with Senthil Kumar K (2026), Appendix A and Theorem A.2, https://doi.org/10.1017/S001309152610145X. This lemma is proved here and is not quoted from the article. A finite summation equivalence over a commutative ring yields coordinate projectors that are idempotent, pairwise annihilating, sum to the identity, have the prescribed submodule ranges, and commute with every endomorphism preserving all summands. No field, finite-dimensionality or nonempty-index assumption is used. Mathlib-only proof; no Prove2Me theorem dependencies or new definitions.

import Mathlib.LinearAlgebra.Pi
import Mathlib.Algebra.Ring.Idempotent

open scoped Classical

theorem WeierstrassEllipticZeta.finite_summation_projector_resolution
    (R M ι : Type*) [CommRing R] [AddCommGroup M] [Module R M] [Fintype ι]
    (E : ι → Submodule R M) (e : (∀ i, E i) ≃ₗ[R] M)
    (he : ∀ x, e x = ∑ i, (x i : M)) :
    ∃ P : ι → Module.End R M,
      (∀ i x, P i x = (e.symm x i : M)) ∧
      (∀ i, IsIdempotentElem (P i)) ∧
      (∀ i j, i ≠ j → P i * P j = 0) ∧
      (∑ i, P i) = 1 ∧
      (∀ i, LinearMap.range (P i) = E i) ∧
      ∀ g : Module.End R M, (∀ i, Set.MapsTo g (E i) (E i)) →
        ∀ i, Commute (P i) g := by sorry
