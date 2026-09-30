-- Prove2me | Theorems.Thm_PhilipponMultiplicity_proposition_3_3_cohenMacaulay
-- name    : PhilipponMultiplicity.proposition_3_3_cohenMacaulay
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-27T10:27:32.505293+00:00
-- url     : https://prove2.me/theorems/d3dfc89c-86ea-4ffd-9601-93ce903481a5
-- title:
--   Proposition 3.3: intersection bound with primary multiplicities on a CM locus
-- statement:
--   Under the original base-field and equation hypotheses of Philippon Proposition 3.3, suppose $I_0$ is locally Cohen–Macaulay at every maximal ideal in the open locus $U$. For $I=I_0+(P_1,\ldots,P_m)$, $$S_UH(I;D)\le S_UH(I_0;D).$$ These are the actual isolated primary-component degree sums, retaining multiplicities. This is exactly the proposition’s second inequality, with no added regularity, slice-dimension or per-cut estimate hypothesis. Its proof remains open.
-- source:
--   Philippon (1986), Lemmes de zéros dans les groupes algébriques commutatifs. Second inequality of Proposition 3.3, printed pp. 365–370, especially the changing open loci and primary-component comparisons on pp. 369–370. This separate dependency retains precisely the source conclusion and hypotheses. https://www.numdam.org/articles/10.24033/bsmf.2060/

import Definitions.Def_PhilipponMultiplicity_SectionThreeSupport
set_option autoImplicit false
open scoped BigOperators
open MvPolynomial PhilipponMultiplicity PhilipponMultiplicity.SectionThree
open PhilipponMultiplicity.SectionThreeSupport PhilipponMultiplicity.Hilbert

theorem PhilipponMultiplicity.proposition_3_3_cohenMacaulay
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (M : MultiProjectiveSpace K)
    (I₀ : Ideal M.CoordinateRing) (hI₀ : IsMultihomogeneousIdeal M I₀)
    (m : ℕ) (P : Fin m → M.CoordinateRing) (D : M.FactorIndex → ℕ)
    (hP : ∀ j, IsMultihomogeneousOfDegreeAtMost M (P j) D)
    (U : MaximalOpenLocus M) (hCM : IsLocallyCohenMacaulayOn M I₀ U) :
    componentHilbertSum M (I₀ ⊔ Ideal.span (Set.range P)) U D ≤
      componentHilbertSum M I₀ U D := by sorry
