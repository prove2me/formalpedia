-- Prove2me | Theorems.Thm_PhilipponMultiplicity_Hilbert_hilbertFunction_colon_add
-- name    : PhilipponMultiplicity.Hilbert.hilbertFunction_colon_add
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-26T01:01:52.790138+00:00
-- url     : https://prove2.me/theorems/5b630648-7bef-4040-bd28-8feae87e19a6
-- title:
--   Colon exact sequence for multigraded Hilbert functions
-- statement:
--   For every multihomogeneous ideal $I$ over a field and every homogeneous polynomial $P$ of multidegree $D$, the actual quotient Hilbert functions satisfy $h_{I+(P)}(D+d)+h_{I:P}(d)=h_I(D+d)$ at every natural multidegree $d$. No non-zero-divisor hypothesis is imposed.
-- source:
--   Supporting commutative algebra for Philippon (1986), Lemmes de zéros dans les groupes algébriques commutatifs, §3, Lemma 3.2, printed p. 364, https://www.numdam.org/articles/10.24033/bsmf.2060/. Philippon refers to the classical homogeneous argument and van der Waerden (1928), Theorem 8 p. 758 and §32 p. 767. This is a proved intermediate step of that associativity argument, not an additional numbered assertion in Philippon.

import Definitions.Def_PhilipponMultiplicity_SectionThree
set_option autoImplicit false
open scoped BigOperators
open MvPolynomial PhilipponMultiplicity PhilipponMultiplicity.SectionThree
open PhilipponMultiplicity.Hilbert

theorem PhilipponMultiplicity.Hilbert.hilbertFunction_colon_add
    {K : Type*} [Field K] (M : MultiProjectiveSpace K)
    (I : Ideal M.CoordinateRing) (hI : IsMultihomogeneousIdeal M I)
    (P : M.CoordinateRing) (D : M.FactorIndex → ℕ) (hP : M.IsHomogeneous P D)
    (d : M.FactorIndex → ℕ) :
    hilbertFunction K M.factorCount M.ambientDimension
        (I ⊔ Ideal.span {P}) (D + d) +
      hilbertFunction K M.factorCount M.ambientDimension (I.colon {P}) d =
    hilbertFunction K M.factorCount M.ambientDimension I (D + d) := by sorry
