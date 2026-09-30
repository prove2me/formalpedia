-- Prove2me | Theorems.Thm_PhilipponMultiplicity_SectionThreeSupport_exists_descending_cut_chain
-- name    : PhilipponMultiplicity.SectionThreeSupport.exists_descending_cut_chain
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-26T09:12:57.70384+00:00
-- url     : https://prove2.me/theorems/783b15cf-a07c-460d-a2d6-4cf2b8dc8685
-- title:
--   Finite dimension-descending regular cuts for Proposition 3.3
-- statement:
--   Let $I_0$ be a multihomogeneous ideal over an infinite field, let $P_1,\ldots,P_m$ be multihomogeneous equations with block degrees bounded by $D$, and put $I=I_0+(P_1,\ldots,P_m)$ and $a=\dim_H I_0$. There exist ideals $J_0,\ldots,J_a$ and cutting equations $F_0,\ldots,F_{a-1}$ with $J_0=I_0$, $I_0\subseteq J_t\subseteq I$ and $J_{t+1}=J_t+(F_t)$. Each $F_t$ lies in the original equation ideal, has exact multidegree $D$, avoids every discarded relevant minimal prime, and is a nonzerodivisor modulo their canonical primary-component intersection. Every such discarded component at stage $t$ has dimension at most $a-t$; above that threshold, the radicals of the dimension truncations of $J_t$ and $I$ agree. At the endpoint, each isolated dimension slice of $J_a$ is contained in the corresponding slice of $I$, and for every open locus and every natural degree vector the radical component sum of $I$ is at most that of $J_a$. The ideals and equations are represented by natural-indexed functions, with conditions only through stage $a$. Zero degree entries and empty equation families are included. This theorem constructs the geometric part of the induction and its radical endpoint comparison; it does not assert either per-cut degree-sum bound or the scheme-theoretic endpoint bound.
-- source:
--   Philippon (1986), Lemmes de zéros dans les groupes algébriques commutatifs, proof of Proposition 3.3, printed pp. 366–368. The geometric induction and final radical comparison are extracted as granular supporting assertions; the numerical bounds along the cuts are separate obligations. https://www.numdam.org/articles/10.24033/bsmf.2060/

import Definitions.Def_PhilipponMultiplicity_SectionThreeSupport
set_option autoImplicit false
open scoped BigOperators
open PhilipponMultiplicity PhilipponMultiplicity.SectionThree
open PhilipponMultiplicity.SectionThreeSupport

theorem PhilipponMultiplicity.SectionThreeSupport.exists_descending_cut_chain
    {K : Type*} [Field K] (M : MultiProjectiveSpace K)
[Infinite K]
    (I₀ : Ideal M.CoordinateRing) (hI₀ : IsMultihomogeneousIdeal M I₀)
    (m : ℕ) (P : Fin m → M.CoordinateRing) (D : M.FactorIndex → ℕ)
    (hP : ∀ j, IsMultihomogeneousOfDegreeAtMost M (P j) D) :
    let I := I₀ ⊔ Ideal.span (Set.range P)
    let a := idealDimension M I₀
    ∃ J : ℕ → Ideal M.CoordinateRing, ∃ F : ℕ → M.CoordinateRing,
      J 0 = I₀ ∧
      (∀ t ≤ a, IsMultihomogeneousIdeal M (J t) ∧ I₀ ≤ J t ∧ J t ≤ I ∧
        (∀ q ∈ (J t).minimalPrimes,
          Hilbert.IsRelevant K M.factorCount M.ambientDimension q →
          q ∉ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I) →
          idealDimension M q ≤ a - t) ∧
        (∀ c, a - t < c →
          (dimensionAtLeast M (J t) c).radical = (dimensionAtLeast M I c).radical)) ∧
      (∀ t < a, J (t + 1) = J t ⊔ Ideal.span {F t} ∧
        F t ∈ Ideal.span (Set.range P) ∧ M.IsHomogeneous (F t) D ∧
        (∀ q ∈ (J t).minimalPrimes,
          Hilbert.IsRelevant K M.factorCount M.ambientDimension q →
          q ∉ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I) → F t ∉ q) ∧
        IsRegular (Ideal.Quotient.mk
          (⨅ q : {q : Hilbert.MinimalComponent K M.factorCount M.ambientDimension (J t) //
            Hilbert.IsRelevant K M.factorCount M.ambientDimension q.1.asIdeal ∧
            q.1.asIdeal ∉ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I)},
            Hilbert.primaryComponent K M.factorCount M.ambientDimension (J t) q.1.1) (F t))) ∧
      (∀ b, dimensionSlice M (J a) b ≤ dimensionSlice M I b) ∧
      (∀ (U : MaximalOpenLocus M) (d : M.FactorIndex → ℕ),
        componentHilbertSum M I.radical U d ≤ componentHilbertSum M (J a).radical U d)  := by sorry
