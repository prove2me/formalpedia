-- Prove2me | Theorems.Thm_PhilipponMultiplicity_SectionThreeSupport_exists_bounded_homogeneous_avoiding
-- name    : PhilipponMultiplicity.SectionThreeSupport.exists_bounded_homogeneous_avoiding
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-26T02:39:06.10693+00:00
-- url     : https://prove2.me/theorems/c82eaf89-698d-4840-b218-3f03c94cb804
-- title:
--   A prescribed-multidegree equation avoiding finitely many relevant primes
-- statement:
--   Over an infinite field, let $P_1,\ldots,P_m$ be multihomogeneous equations of degrees at most $D$. Suppose each of finitely many relevant primes contains $I_0$ but does not contain $I_0+(P_1,\ldots,P_m)$. There is an $f\in(P_1,\ldots,P_m)$, homogeneous of exact multidegree $D$, outside all those primes. No positivity of the coordinates of $D$ is required.
-- source:
--   Philippon (1986), Lemmes de zéros dans les groupes algébriques commutatifs, equation selection in the proof of Proposition 3.3, printed p. 367, https://www.numdam.org/articles/10.24033/bsmf.2060/. A granular supporting assertion for the original Section 3 statements; definitions are unchanged.

import Definitions.Def_PhilipponMultiplicity_SectionThreeSupport
set_option autoImplicit false
open scoped BigOperators
open MvPolynomial PhilipponMultiplicity PhilipponMultiplicity.SectionThree
open PhilipponMultiplicity.SectionThreeSupport PhilipponMultiplicity.Hilbert

theorem PhilipponMultiplicity.SectionThreeSupport.exists_bounded_homogeneous_avoiding
    {K : Type*} [Field K] [Infinite K] (M : MultiProjectiveSpace K) {ι : Type*} [Finite ι]
    (I₀ : Ideal M.CoordinateRing) (m : ℕ) (P : Fin m → M.CoordinateRing)
    (D : M.FactorIndex → ℕ)
    (hP : ∀ j, IsMultihomogeneousOfDegreeAtMost M (P j) D)
    (q : ι → Ideal M.CoordinateRing) (hq : ∀ i, (q i).IsPrime)
    (hrel : ∀ i, Hilbert.IsRelevant K M.factorCount M.ambientDimension (q i))
    (hI₀ : ∀ i, I₀ ≤ q i)
    (havoid : ∀ i, ¬ I₀ ⊔ Ideal.span (Set.range P) ≤ q i) :
    ∃ f : M.CoordinateRing, f ∈ Ideal.span (Set.range P) ∧
      M.IsHomogeneous f D ∧ ∀ i, f ∉ q i := by sorry
