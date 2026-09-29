-- Prove2me | Theorems.Thm_ValuationSubring_normal_residueField_and_forall_algEquiv_exists_smul_eq_of_isGalois
-- name    : ValuationSubring.normal_residueField_and_forall_algEquiv_exists_smul_eq_of_isGalois
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/72d22faf-f75a-52fc-b5e6-f1513c5a3e02
-- title:
--   Hilbert theory for valuation rings in a finite Galois extension
-- statement:
--   Let $E$ be a field and $F$ a finite-dimensional Galois extension of $E$, let $O$ be a valuation subring of $E$ and $O'$ a valuation subring of $F$ lying over $O$, in the sense that for every $x \in E$ one has $\mathrm{algebraMap}_{E,F}(x) \in O'$ if and only if $x \in O$. Suppose the residue field of $O'$ is given the structure of an algebra over the residue field of $O$, compatibly with the inclusion: for every $a \in O$, the structure map carries the residue class of $a$ to the residue class of the element of $O'$ given by the image of $a$ in $F$. Then three assertions hold simultaneously. First, every $\sigma$ in the decomposition subgroup of $O'$ over $E$ (the $E$-algebra automorphisms of $F$ preserving $O'$, acting on the residue field of $O'$) fixes each element of the image of the residue field of $O$ in the residue field of $O'$. Second, the residue field of $O'$ is a normal extension of the residue field of $O$. Third, every automorphism $\tau$ of the residue field of $O'$ over the residue field of $O$ is induced by some $\sigma$ in the decomposition subgroup: $\sigma \cdot x = \tau(x)$ for all $x$ in the residue field of $O'$.
--
--   This is the classical Hilbert decomposition theory for a valuation ring in a finite Galois extension: the residue extension is normal and the decomposition group surjects onto its automorphism group, the kernel being the inertia subgroup. It is used in the construction of Frobenius elements at a valuation with discrete, hence residually well-behaved, valuation ring, via [`ValuationSubring.exists_isFrobeniusAt_pow_of_isDiscreteValuationRing`](thm.html#ValuationSubring.exists_isFrobeniusAt_pow_of_isDiscreteValuationRing); the proof cites the comparison of valuation subrings of $F$ over $O$ with maximal ideals of the integral closure of $O$ in $F$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_normal_residueField_and_forall_algEquiv_exists_smul_eq_of_isGalois.lean

import Mathlib.RingTheory.Valuation.RamificationGroup
import Mathlib.FieldTheory.Galois.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ValuationSubring.normal_residueField_and_forall_algEquiv_exists_smul_eq_of_isGalois
    {E F : Type*} [Field E] [Field F] [Algebra E F]
    [FiniteDimensional E F]
    [IsGalois E F]
    (O : ValuationSubring E)
    (O' : ValuationSubring F)
    (hO : ∀ x : E, algebraMap E F x ∈ O' ↔ x ∈ O)
    [Algebra (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O')]
    (hcompat : ∀ a : O, algebraMap (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O')
        (IsLocalRing.residue O a) = IsLocalRing.residue O' ⟨algebraMap E F a, (hO a).mpr a.2⟩) :
    (∀ (σ : O'.decompositionSubgroup E) (a : IsLocalRing.ResidueField O),
        σ • algebraMap (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O') a =
          algebraMap (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O') a) ∧
    Normal (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O') ∧
    ∀ τ : IsLocalRing.ResidueField O' ≃ₐ[IsLocalRing.ResidueField O] IsLocalRing.ResidueField O',
      ∃ σ : O'.decompositionSubgroup E, ∀ x : IsLocalRing.ResidueField O', σ • x = τ x := by sorry
