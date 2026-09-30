-- Prove2me | Theorems.Thm_PhilipponMultiplicity_proposition_3_3_radical
-- name    : PhilipponMultiplicity.proposition_3_3_radical
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-27T10:27:24.503368+00:00
-- url     : https://prove2.me/theorems/38cb51cb-ec98-45ab-986c-d52848597737
-- title:
--   Proposition 3.3: the complete reduced intersection inequality
-- statement:
--   Let $I_0$ be a multihomogeneous ideal over an infinite field and let $I=I_0+(P_1,\ldots,P_m)$, where the homogeneous equations have block degrees at most $D$. For every open locus $U$, $$S_UH(\sqrt I;D)\le S_UH(\sqrt{I_0};D).$$ This proves the first inequality of Philippon Proposition 3.3 when $U$ is the whole maximal spectrum, with the stronger open-locus conclusion stated explicitly. It concerns reduced components; it does not prove the second inequality retaining primary multiplicities.
-- source:
--   Philippon (1986), Lemmes de zéros dans les groupes algébriques commutatifs. First inequality of Proposition 3.3, printed pp. 365–368. The source’s finite descending cut chain and final component comparison are reused. The support theorem is valid over every infinite field and on every open locus; the original proposition is recovered at the full locus. https://www.numdam.org/articles/10.24033/bsmf.2060/

import Definitions.Def_PhilipponMultiplicity_SectionThreeSupport
set_option autoImplicit false
open scoped BigOperators
open MvPolynomial PhilipponMultiplicity PhilipponMultiplicity.SectionThree
open PhilipponMultiplicity.SectionThreeSupport PhilipponMultiplicity.Hilbert

theorem PhilipponMultiplicity.proposition_3_3_radical {K : Type*} [Field K] [Infinite K]
    (M : MultiProjectiveSpace K)
    (I₀ : Ideal M.CoordinateRing) (hI₀ : IsMultihomogeneousIdeal M I₀)
    (m : ℕ) (P : Fin m → M.CoordinateRing) (D : M.FactorIndex → ℕ)
    (hP : ∀ j, IsMultihomogeneousOfDegreeAtMost M (P j) D)
    (U : MaximalOpenLocus M) :
    componentHilbertSum M (I₀ ⊔ Ideal.span (Set.range P)).radical U D ≤
      componentHilbertSum M I₀.radical U D := by sorry
