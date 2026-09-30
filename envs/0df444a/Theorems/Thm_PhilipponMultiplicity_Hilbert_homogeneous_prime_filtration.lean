-- Prove2me | Theorems.Thm_PhilipponMultiplicity_Hilbert_homogeneous_prime_filtration
-- name    : PhilipponMultiplicity.Hilbert.homogeneous_prime_filtration
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-26T01:02:03.146876+00:00
-- url     : https://prove2.me/theorems/1fe6d915-3846-4b0f-bff3-426c27aec4ae
-- title:
--   Finite homogeneous prime filtration of a polynomial quotient
-- statement:
--   Every multihomogeneous ideal $I$ in a product-of-projective-spaces coordinate ring over a field admits a finite chain $I=J_0\subsetneq J_1\subsetneq\cdots\subsetneq J_n=R$. All ideals in the chain are multihomogeneous. Each step has $J_{j+1}=J_j+(P_j)$ with $P_j$ homogeneous, $P_j\notin J_j$, and $J_j:P_j$ prime. Thus the successive cyclic factors are degree shifts of actual prime quotients.
-- source:
--   Supporting commutative algebra for Philippon (1986), Lemmes de zéros dans les groupes algébriques commutatifs, §3, Lemma 3.2, printed p. 364, https://www.numdam.org/articles/10.24033/bsmf.2060/. Philippon refers to the classical homogeneous argument and van der Waerden (1928), Theorem 8 p. 758 and §32 p. 767. This is a proved intermediate step of that associativity argument, not an additional numbered assertion in Philippon.

import Definitions.Def_PhilipponMultiplicity_SectionThree
set_option autoImplicit false
open scoped BigOperators
open MvPolynomial PhilipponMultiplicity PhilipponMultiplicity.SectionThree
open PhilipponMultiplicity.Hilbert

theorem PhilipponMultiplicity.Hilbert.homogeneous_prime_filtration
    {K : Type*} [Field K] (M : MultiProjectiveSpace K) (I : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I) :
    ∃ n : ℕ, ∃ J : Fin (n + 1) → Ideal M.CoordinateRing,
      ∃ P : Fin n → M.CoordinateRing, ∃ D : Fin n → M.FactorIndex → ℕ,
      J 0 = I ∧ J (Fin.last n) = ⊤ ∧
      (∀ j, IsMultihomogeneousIdeal M (J j)) ∧
      (∀ j, M.IsHomogeneous (P j) (D j) ∧ P j ∉ J j.castSucc ∧
        J j.succ = J j.castSucc ⊔ Ideal.span {P j} ∧
        ((J j.castSucc).colon {P j}).IsPrime) := by sorry
