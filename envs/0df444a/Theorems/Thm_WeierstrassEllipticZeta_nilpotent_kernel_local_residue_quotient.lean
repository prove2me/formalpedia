-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_nilpotent_kernel_local_residue_quotient
-- name    : WeierstrassEllipticZeta.nilpotent_kernel_local_residue_quotient
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-12T17:47:17.987211+00:00
-- url     : https://prove2.me/theorems/c416b1d5-0beb-42c2-8330-cb4d4e316396
-- title:
--   Local algebra and residue quotient from a nilpotent-kernel character
-- statement:
--   Let $K$ be a field, let $A$ be a commutative $K$-algebra, and let $\chi:A\to K$ be a $K$-algebra homomorphism. Suppose
--
--   $$
--   \chi(a)=0\quad\Longleftrightarrow\quad a\text{ is nilpotent}
--   \qquad(a\in A).
--   $$
--
--   Write $N$ for the nilradical of $A$, the ideal of all nilpotent elements. Then $A$ is a local ring, $N$ is maximal, and $N$ is the only prime ideal of $A$. Moreover, there is a $K$-algebra isomorphism
--
--   $$
--   e:A/N\xrightarrow{\ \sim\ }K,
--   \qquad e(a+N)=\chi(a).
--   $$
--
--   Thus the character identifies the reduced quotient of $A$ with the base field and determines its unique prime and maximal ideal. No polynomial-generation, finite-dimensionality, or characteristic-zero hypothesis is required.
-- source:
--   Derived supporting algebra for the Senthil Kumar mission. For a commutative K-algebra with a K-algebra character to K whose kernel consists exactly of nilpotent elements, the nilradical is maximal and is the unique prime ideal, the algebra is local, and quotienting by the nilradical gives a K-algebra isomorphism to K with the prescribed character on representatives. No cyclicity, finite-dimensionality or characteristic-zero hypothesis is needed. This is inferred supporting algebra, not a quoted theorem of the article. Pinned Mathlib revision 0df444a360eaa60ab8c11dca51a86af692955474: RingTheory/Ideal/Maps.lean, RingHom.ker_isMaximal_of_surjective; RingTheory/Nilpotent/Lemmas.lean, mem_nilradical and nilradical_le_prime; RingTheory/LocalRing/Basic.lean, IsLocalRing.of_unique_max_ideal; RingTheory/Ideal/Quotient/Operations.lean, Ideal.quotientKerAlgEquivOfSurjective. Primary documentation: https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Nilpotent/Lemmas.html and https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Ideal/Quotient/Operations.html . No new definitions or platform dependencies.

import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.Nilpotent.Lemmas

theorem WeierstrassEllipticZeta.nilpotent_kernel_local_residue_quotient
    (K A : Type*) [Field K] [CommRing A] [Algebra K A]
    (χ : A →ₐ[K] K) (hnil : ∀ a : A, χ a = 0 ↔ IsNilpotent a) :
    IsLocalRing A ∧ (nilradical A).IsMaximal ∧
      (∀ J : Ideal A, J.IsPrime ↔ J = nilradical A) ∧
      ∃ e : (A ⧸ nilradical A) ≃ₐ[K] K,
        ∀ a : A, e (Ideal.Quotient.mk (nilradical A) a) = χ a := by sorry
