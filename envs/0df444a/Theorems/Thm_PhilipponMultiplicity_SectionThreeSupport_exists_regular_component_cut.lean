-- Prove2me | Theorems.Thm_PhilipponMultiplicity_SectionThreeSupport_exists_regular_component_cut
-- name    : PhilipponMultiplicity.SectionThreeSupport.exists_regular_component_cut
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-26T02:39:29.602108+00:00
-- url     : https://prove2.me/theorems/2d454499-5713-400a-8043-b73967184e1b
-- title:
--   A regular cutting equation on the selected discarded components
-- statement:
--   Let $I_0\subseteq J\subseteq I_0+(P_1,\ldots,P_m)$, with the $P_j$ homogeneous of multidegrees at most $D$ over an infinite field. Select finitely many relevant minimal primes of $J$ that are not associated to the final ideal. There is an equation in $(P_1,\ldots,P_m)$ of exact degree $D$ avoiding all selected primes and regular modulo the intersection of their actual canonical primary components.
-- source:
--   Philippon (1986), Lemmes de zéros dans les groupes algébriques commutatifs, regular equation selection in Proposition 3.3, printed p. 367, https://www.numdam.org/articles/10.24033/bsmf.2060/. A granular supporting assertion for the original Section 3 statements; definitions are unchanged.

import Definitions.Def_PhilipponMultiplicity_SectionThreeSupport
set_option autoImplicit false
open scoped BigOperators
open MvPolynomial PhilipponMultiplicity PhilipponMultiplicity.SectionThree
open PhilipponMultiplicity.SectionThreeSupport PhilipponMultiplicity.Hilbert

theorem PhilipponMultiplicity.SectionThreeSupport.exists_regular_component_cut
    {K : Type*} [Field K] [Infinite K] (M : MultiProjectiveSpace K) {ι : Type*} [Finite ι]
    (I₀ J : Ideal M.CoordinateRing) (hI₀J : I₀ ≤ J)
    (m : ℕ) (P : Fin m → M.CoordinateRing) (D : M.FactorIndex → ℕ)
    (hP : ∀ j, IsMultihomogeneousOfDegreeAtMost M (P j) D)
    (hJI : J ≤ I₀ ⊔ Ideal.span (Set.range P))
    (q : ι → Hilbert.MinimalComponent K M.factorCount M.ambientDimension J)
    (hrel : ∀ i, Hilbert.IsRelevant K M.factorCount M.ambientDimension (q i).1.asIdeal)
    (hdiscard : ∀ i, (q i).1.asIdeal ∉ associatedPrimes M.CoordinateRing
      (M.CoordinateRing ⧸ (I₀ ⊔ Ideal.span (Set.range P)))) :
    ∃ f : M.CoordinateRing, f ∈ Ideal.span (Set.range P) ∧ M.IsHomogeneous f D ∧
      (∀ i, f ∉ (q i).1.asIdeal) ∧
      IsRegular (Ideal.Quotient.mk
        (⨅ i, Hilbert.primaryComponent K M.factorCount M.ambientDimension J (q i).1) f) := by sorry
