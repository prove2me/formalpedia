-- Prove2me | Theorems.Thm_ValuationSubring_exists_intermediateField_le_isDiscreteValuationRing_henselianLocalRing_comap_of_finiteDimensional
-- name    : ValuationSubring.exists_intermediateField_le_isDiscreteValuationRing_henselianLocalRing_comap_of_finiteDimensional
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.105901+00:00
-- url     : https://prove2.me/theorems/bdd9cee1-6dc9-582d-b0f1-ed5aaa418cd5
-- title:
--   Henselian DVR at the decomposition field over a finite extension
-- statement:
--   Let $R$ be a discrete valuation ring which is a domain, let $K$ be a field equipped with an $R$-algebra structure making it the fraction field of $R$, and let $\Omega$ be an algebraic closure of $K$, all in one universe. Let $A$ be a valuation subring of $\Omega$ such that the image in $\Omega$ of every element of $R$ lies in $A$, and assume $A \neq \Omega$. Let $K' \subseteq \Omega$ be an intermediate field of $\Omega/K$ which is finite-dimensional over $K$. Then there exists an intermediate field $K^{h}$ of $\Omega/K$ with the following three properties: first, $K' \le K^{h}$; second, every $K$-algebra automorphism $\sigma$ of $\Omega$ lying in the decomposition subgroup of $A$ over $K$ (that is, stabilising $A$ under the pointwise action) and fixing every element of $K'$ fixes every element of $K^{h}$; third, the valuation subring $A \cap K^{h}$ of $K^{h}$, i.e. the pullback of $A$ along the inclusion $K^{h} \to \Omega$, is a discrete valuation ring and is a henselian local ring.
--
--   This is the construction of the decomposition field of a place of $\Omega$ over a finite extension $K'/K$, whose associated valuation ring is the henselisation of $A \cap K'$ and is therefore a henselian discrete valuation ring; the two extra clauses record that $K^{h}$ contains $K'$ and is fixed by the part of the decomposition group fixing $K'$. It supplies the henselian base needed in the analysis of the Tate module of a fake elliptic curve in the Čerednik–Drinfel'd part of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_exists_intermediateField_le_isDiscreteValuationRing_henselianLocalRing_comap_of_finiteDimensional.lean

import Mathlib
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem ValuationSubring.exists_intermediateField_le_isDiscreteValuationRing_henselianLocalRing_comap_of_finiteDimensional
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type u} [Field K] [Algebra R K] [IsFractionRing R K]
    {Ω : Type u} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (A : ValuationSubring Ω) (hA : ∀ r : R, algebraMap K Ω (algebraMap R K r) ∈ A) (hAtop : A ≠ ⊤)
    (K' : IntermediateField K Ω) [FiniteDimensional K ↥K'] :
    ∃ Kh : IntermediateField K Ω, K' ≤ Kh ∧
      (∀ σ : Ω ≃ₐ[K] Ω, σ ∈ A.decompositionSubgroup K → (∀ x : Ω, x ∈ K' → σ x = x) →
        ∀ x : Ω, x ∈ Kh → σ x = x) ∧
      IsDiscreteValuationRing ↥(A.comap (algebraMap ↥Kh Ω)) ∧
      HenselianLocalRing ↥(A.comap (algebraMap ↥Kh Ω)) := by sorry
