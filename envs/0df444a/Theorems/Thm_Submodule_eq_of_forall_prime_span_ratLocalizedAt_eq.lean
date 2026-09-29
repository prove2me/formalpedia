-- Prove2me | Theorems.Thm_Submodule_eq_of_forall_prime_span_ratLocalizedAt_eq
-- name    : Submodule.eq_of_forall_prime_span_ratLocalizedAt_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.134728+00:00
-- url     : https://prove2.me/theorems/0854b745-b689-5111-9591-2fd0953401ce
-- title:
--   A ℤ-submodule of a ℚ-vector space is determined by its localisations
-- statement:
--   Let $V$ be an additive commutative group equipped with a $\mathbf{Q}$-module structure, and let $M$ and $N$ be two $\mathbf{Z}$-submodules of $V$. For a natural number $p$, write $\mathbf{Z}_{(p)}$ for the subring [`GaloisRep.ratLocalizedAt p`](def/GaloisRep_Flat.html#L8) of $\mathbf{Q}$ whose elements are the rationals $q$ whose denominator $q.\mathrm{den}$ is coprime to $p$ (the subring axioms holding because the denominator of a sum or product divides the product of the denominators). Assume that for every natural number $\ell$ that is prime, the $\mathbf{Z}_{(\ell)}$-submodule of $V$ spanned by the underlying set of $M$ coincides with the $\mathbf{Z}_{(\ell)}$-submodule spanned by the underlying set of $N$. The conclusion is that $M = N$ as $\mathbf{Z}$-submodules of $V$. No finiteness, freeness or non-degeneracy hypothesis is imposed on $M$, $N$ or $V$.
--
--   This is the local-global principle $M = \bigcap_{\ell} M_{(\ell)}$ for $\mathbf{Z}$-submodules of a $\mathbf{Q}$-vector space: a lattice is recovered from its localisations at all primes. It serves as the gluing step when objects over $\mathbf{Z}$ are reconstructed from local data, and is used in the classification of Hopf orders underlying [`HopfAlgebra.nonempty_bialgEquiv_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_ne_two`](thm.html#HopfAlgebra.nonempty_bialgEquiv_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_ne_two) and [`HopfAlgebra.prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two`](thm.html#HopfAlgebra.prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Submodule_eq_of_forall_prime_span_ratLocalizedAt_eq.lean

import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Int.Basic
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Algebra.Module.Rat
import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem Submodule.eq_of_forall_prime_span_ratLocalizedAt_eq
    {V : Type*} [AddCommGroup V] [Module ℚ V] (M N : Submodule ℤ V)
    (h : ∀ ℓ : ℕ, ℓ.Prime →
      Submodule.span (GaloisRep.ratLocalizedAt ℓ) (M : Set V) =
        Submodule.span (GaloisRep.ratLocalizedAt ℓ) (N : Set V)) : M = N := by sorry
