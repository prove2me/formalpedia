-- Prove2me | Theorems.Thm_Submodule_mem_span_ratLocalizedAt_iff
-- name    : Submodule.mem_span_ratLocalizedAt_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.134728+00:00
-- url     : https://prove2.me/theorems/f4f9a868-953b-5e67-947f-b84e8974371c
-- title:
--   Membership in the ℤ_{(ℓ)}-span: denominators prime to ℓ
-- statement:
--   Let $V$ be an additive commutative group equipped with a $\mathbf{Q}$-module structure, let $M$ be a $\mathbf{Z}$-submodule of $V$, let $\ell$ be a natural number with $\ell$ prime, and let $x \in V$. Write $R_\ell$ for the subring [`GaloisRep.ratLocalizedAt ℓ`](def/GaloisRep_Flat.html#L8) of $\mathbf{Q}$ consisting of those rationals $q$ whose denominator `q.den` is coprime to $\ell$ (this is a subring: the carrier contains $0$ and $1$ and is closed under negation, addition and multiplication, since the denominator of a sum or product divides the product of the denominators). Via restriction of scalars along $R_\ell \subseteq \mathbf{Q}$, the space $V$ is an $R_\ell$-module, and one may form the $R_\ell$-submodule of $V$ spanned by the underlying set of $M$. The assertion is that $x$ lies in this $R_\ell$-span if and only if there exists an integer $s$ with $(\ell : \mathbf{Z})$ not dividing $s$ and $s \cdot x \in M$ (the $\mathbf{Z}$-action on $V$).
--
--   This identifies the localisation at $\ell$ of a $\mathbf{Z}$-lattice inside a $\mathbf{Q}$-vector space, written as a span over the subring of rationals with denominator prime to $\ell$, with the elementary description by integral multiples with denominator prime to $\ell$. It is used for the statement that a $\mathbf{Z}$-submodule of a $\mathbf{Q}$-vector space is determined by its localisations at all primes ([`Submodule.eq_of_forall_prime_span_ratLocalizedAt_eq`](thm.html#Submodule.eq_of_forall_prime_span_ratLocalizedAt_eq)), and in the Hopf-algebra argument [`HopfAlgebra.prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two`](thm.html#HopfAlgebra.prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Submodule_mem_span_ratLocalizedAt_iff.lean

import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Int.Basic
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Algebra.Module.Rat
import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem Submodule.mem_span_ratLocalizedAt_iff
    {V : Type*} [AddCommGroup V] [Module ℚ V] (M : Submodule ℤ V) (ℓ : ℕ) (hℓ : ℓ.Prime) (x : V) :
    x ∈ Submodule.span (GaloisRep.ratLocalizedAt ℓ) (M : Set V) ↔
      ∃ s : ℤ, ¬ (ℓ : ℤ) ∣ s ∧ s • x ∈ M := by sorry
