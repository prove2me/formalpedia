-- Prove2me | Theorems.Thm_PhilipponMultiplicity_Hilbert_localLength_eq_filtration_count
-- name    : PhilipponMultiplicity.Hilbert.localLength_eq_filtration_count
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-26T01:01:50.52012+00:00
-- url     : https://prove2.me/theorems/5bb0dd38-ca6a-43e4-b1b4-9811ccedace6
-- title:
--   Generic localized length counts prime-filtration factors
-- statement:
--   Let $I=J_0\subseteq\cdots\subseteq J_n=R$ be a finite cyclic filtration with $J_{j+1}=J_j+(P_j)$ and each $J_j:P_j$ prime. At every actual minimal prime $q$ over $I$, the actual generic length $\ell_{R_q}(R_q/IR_q)$ is the number of indices $j$ with $J_j:P_j=q$. The length is the existing localized module-length definition, converted to a natural number; no multiplicity is supplied as data.
-- source:
--   Supporting commutative algebra for Philippon (1986), Lemmes de zéros dans les groupes algébriques commutatifs, §3, Lemma 3.2, printed p. 364, https://www.numdam.org/articles/10.24033/bsmf.2060/. Philippon refers to the classical homogeneous argument and van der Waerden (1928), Theorem 8 p. 758 and §32 p. 767. This is a proved intermediate step of that associativity argument, not an additional numbered assertion in Philippon.

import Definitions.Def_PhilipponMultiplicity_SectionThree
set_option autoImplicit false
open scoped BigOperators
open MvPolynomial PhilipponMultiplicity PhilipponMultiplicity.SectionThree
open PhilipponMultiplicity.Hilbert

theorem PhilipponMultiplicity.Hilbert.localLength_eq_filtration_count
    {K : Type*} [Field K] (M : MultiProjectiveSpace K) (I : Ideal M.CoordinateRing) (n : ℕ)
    (J : Fin (n + 1) → Ideal M.CoordinateRing) (P : Fin n → M.CoordinateRing)
    (hfirst : J 0 = I) (hlast : J (Fin.last n) = ⊤)
    (hstep : ∀ j, J j.succ = J j.castSucc ⊔ Ideal.span {P j})
    (hprime : ∀ j, ((J j.castSucc).colon {P j}).IsPrime)
    (q : PrimeSpectrum M.CoordinateRing) (hq : q.asIdeal ∈ I.minimalPrimes) :
    (localLength K M.factorCount M.ambientDimension I q).toNat =
      ∑ j, if (J j.castSucc).colon {P j} = q.asIdeal then 1 else 0 := by sorry
