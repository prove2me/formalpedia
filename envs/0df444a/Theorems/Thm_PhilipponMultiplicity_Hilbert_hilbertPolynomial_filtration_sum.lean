-- Prove2me | Theorems.Thm_PhilipponMultiplicity_Hilbert_hilbertPolynomial_filtration_sum
-- name    : PhilipponMultiplicity.Hilbert.hilbertPolynomial_filtration_sum
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-26T01:02:19.087141+00:00
-- url     : https://prove2.me/theorems/ad01ff37-1466-43e9-9317-9fd1d8f41eb2
-- title:
--   Hilbert polynomial as a sum along a homogeneous cyclic filtration
-- statement:
--   For any finite homogeneous ideal chain ending at the unit ideal, with step $J_{j+1}=J_j+(P_j)$ and $P_j$ of multidegree $D_j$, the actual Hilbert polynomial of $J_0$ equals $\sum_j H_{J_j:P_j}(X-D_j)$. The statement holds for every such chain; primality of the colon ideals is not needed.
-- source:
--   Supporting commutative algebra for Philippon (1986), Lemmes de zéros dans les groupes algébriques commutatifs, §3, Lemma 3.2, printed p. 364, https://www.numdam.org/articles/10.24033/bsmf.2060/. Philippon refers to the classical homogeneous argument and van der Waerden (1928), Theorem 8 p. 758 and §32 p. 767. This is a proved intermediate step of that associativity argument, not an additional numbered assertion in Philippon.

import Definitions.Def_PhilipponMultiplicity_SectionThree
set_option autoImplicit false
open scoped BigOperators
open MvPolynomial PhilipponMultiplicity PhilipponMultiplicity.SectionThree
open PhilipponMultiplicity.Hilbert

theorem PhilipponMultiplicity.Hilbert.hilbertPolynomial_filtration_sum
    {K : Type*} [Field K] (M : MultiProjectiveSpace K) (n : ℕ)
    (J : Fin (n + 1) → Ideal M.CoordinateRing)
    (P : Fin n → M.CoordinateRing) (D : Fin n → M.FactorIndex → ℕ)
    (hhom : ∀ j, IsMultihomogeneousIdeal M (J j))
    (hstep : ∀ j, M.IsHomogeneous (P j) (D j) ∧
      J j.succ = J j.castSucc ⊔ Ideal.span {P j})
    (hlast : J (Fin.last n) = ⊤) :
    hilbertPolynomial K M.factorCount M.ambientDimension (J 0) =
      ∑ j, aeval (fun i => X i - C (D j i : ℚ))
        (hilbertPolynomial K M.factorCount M.ambientDimension
          ((J j.castSucc).colon {P j})) := by sorry
