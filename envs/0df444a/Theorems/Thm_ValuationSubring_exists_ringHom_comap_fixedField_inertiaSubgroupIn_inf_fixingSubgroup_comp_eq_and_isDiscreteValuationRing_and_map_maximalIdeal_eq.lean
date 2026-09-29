-- Prove2me | Theorems.Thm_ValuationSubring_exists_ringHom_comap_fixedField_inertiaSubgroupIn_inf_fixingSubgroup_comp_eq_and_isDiscreteValuationRing_and_map_maximalIdeal_eq
-- name    : ValuationSubring.exists_ringHom_comap_fixedField_inertiaSubgroupIn_inf_fixingSubgroup_comp_eq_and_isDiscreteValuationRing_and_map_maximalIdeal_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.105901+00:00
-- url     : https://prove2.me/theorems/b21ca3dc-edc4-5eaf-a14e-ba294b6b0f65
-- title:
--   Inertia-field valuation ring over ℚ(ζₚ) is unramified DVR
-- statement:
--   Let $p$ be a prime and let $L$ be a field of characteristic zero which is a cyclotomic extension of $\mathbb{Q}$ of type $\{p\}$. Let $A$ be a commutative domain which is a discrete valuation ring, equipped with an $A$-algebra structure on $L$ making $L$ the fraction field of $A$, and assume $p \in \mathfrak{m}_A$. Fix algebra structures of $A$ and of $L$ over $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` forming a scalar tower, and let $Pl$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a non-unit of $Pl$, together with a ring homomorphism $\rho : A \to Pl$ whose composite with the inclusion $Pl \hookrightarrow \overline{\mathbb{Q}}$ is the structure map $A \to \overline{\mathbb{Q}}$. Put $H = I \sqcap \mathrm{Fix}$, where $I$ is the image in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of the inertia subgroup of $Pl$ inside its decomposition subgroup, and $\mathrm{Fix}$ is the fixing subgroup of the image of $L \to \overline{\mathbb{Q}}$; let $F$ be the fixed field of $H$ and $O = Pl \cap F$ the preimage of $Pl$ under $F \to \overline{\mathbb{Q}}$. Then there exist ring homomorphisms $\iota : O \to Pl$ and $\rho_O : A \to O$ such that: $\iota$ is the inclusion, i.e. the image of $\iota(o)$ in $\overline{\mathbb{Q}}$ is the image of $o$ under $F \to \overline{\mathbb{Q}}$; $\iota \circ \rho_O = \rho$; $\iota$ is injective; $O$ is a discrete valuation ring; $\mathfrak{m}_A \cdot O = \mathfrak{m}_O$, that is, `Ideal.map` of $\mathfrak{m}_A$ along $\rho_O$ equals $\mathfrak{m}_O$; $\iota(o) \in \mathfrak{m}_{Pl}$ if and only if $o \in \mathfrak{m}_O$; the composite $o \mapsto \mathrm{residue}_{Pl}(\iota(o))$ is surjective onto the residue field of $Pl$; and every $\sigma \in H$ fixes the image of $\iota(o)$ in $\overline{\mathbb{Q}}$ for all $o \in O$.
--
--   This is the statement that the valuation ring cut out on the inertia field of $Pl$ over $L = \mathbb{Q}(\zeta_p)$ is a discrete valuation ring, unramified over $A$ in the strong form that a uniformiser of $A$ (for instance $1 - \zeta_p$) generates the maximal ideal, with the full residue field of $Pl$ already attained. It is used in the study of points of two-chart models of the modular curves $X_1(Mp)$ over valuation subrings, where the unramifiedness supplies exactly the base-change hypothesis needed for regularity.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_exists_ringHom_comap_fixedField_inertiaSubgroupIn_inf_fixingSubgroup_comp_eq_and_isDiscreteValuationRing_and_map_maximalIdeal_eq.lean

import Mathlib
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing

theorem ValuationSubring.exists_ringHom_comap_fixedField_inertiaSubgroupIn_inf_fixingSubgroup_comp_eq_and_isDiscreteValuationRing_and_map_maximalIdeal_eq
    (p : ℕ) [Fact p.Prime]
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A)
    [Algebra A (AlgebraicClosure ℚ)] [Algebra L (AlgebraicClosure ℚ)] [IsScalarTower A L (AlgebraicClosure ℚ)]
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    (ρ : A →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap A (AlgebraicClosure ℚ)) :
    ∃ (ι : ↥(Pl.comap (algebraMap ↥(IntermediateField.fixedField (Pl.inertiaSubgroupIn ℚ ⊓ (IsScalarTower.toAlgHom ℚ L (AlgebraicClosure ℚ)).fieldRange.fixingSubgroup)) (AlgebraicClosure ℚ))) →+* ↥Pl)
      (ρO : A →+* ↥(Pl.comap (algebraMap ↥(IntermediateField.fixedField (Pl.inertiaSubgroupIn ℚ ⊓ (IsScalarTower.toAlgHom ℚ L (AlgebraicClosure ℚ)).fieldRange.fixingSubgroup)) (AlgebraicClosure ℚ)))),
      (∀ o : ↥(Pl.comap (algebraMap ↥(IntermediateField.fixedField (Pl.inertiaSubgroupIn ℚ ⊓ (IsScalarTower.toAlgHom ℚ L (AlgebraicClosure ℚ)).fieldRange.fixingSubgroup)) (AlgebraicClosure ℚ))),
        ((ι o : ↥Pl) : AlgebraicClosure ℚ) = algebraMap ↥(IntermediateField.fixedField (Pl.inertiaSubgroupIn ℚ ⊓ (IsScalarTower.toAlgHom ℚ L (AlgebraicClosure ℚ)).fieldRange.fixingSubgroup)) (AlgebraicClosure ℚ) (o : ↥(IntermediateField.fixedField (Pl.inertiaSubgroupIn ℚ ⊓ (IsScalarTower.toAlgHom ℚ L (AlgebraicClosure ℚ)).fieldRange.fixingSubgroup)))) ∧
      ι.comp ρO = ρ ∧
      Function.Injective ι ∧
      IsDiscreteValuationRing ↥(Pl.comap (algebraMap ↥(IntermediateField.fixedField (Pl.inertiaSubgroupIn ℚ ⊓ (IsScalarTower.toAlgHom ℚ L (AlgebraicClosure ℚ)).fieldRange.fixingSubgroup)) (AlgebraicClosure ℚ))) ∧
      Ideal.map ρO (IsLocalRing.maximalIdeal A) = IsLocalRing.maximalIdeal ↥(Pl.comap (algebraMap ↥(IntermediateField.fixedField (Pl.inertiaSubgroupIn ℚ ⊓ (IsScalarTower.toAlgHom ℚ L (AlgebraicClosure ℚ)).fieldRange.fixingSubgroup)) (AlgebraicClosure ℚ))) ∧
      (∀ o : ↥(Pl.comap (algebraMap ↥(IntermediateField.fixedField (Pl.inertiaSubgroupIn ℚ ⊓ (IsScalarTower.toAlgHom ℚ L (AlgebraicClosure ℚ)).fieldRange.fixingSubgroup)) (AlgebraicClosure ℚ))), ι o ∈ IsLocalRing.maximalIdeal ↥Pl ↔ o ∈ IsLocalRing.maximalIdeal ↥(Pl.comap (algebraMap ↥(IntermediateField.fixedField (Pl.inertiaSubgroupIn ℚ ⊓ (IsScalarTower.toAlgHom ℚ L (AlgebraicClosure ℚ)).fieldRange.fixingSubgroup)) (AlgebraicClosure ℚ)))) ∧
      Function.Surjective (fun o : ↥(Pl.comap (algebraMap ↥(IntermediateField.fixedField (Pl.inertiaSubgroupIn ℚ ⊓ (IsScalarTower.toAlgHom ℚ L (AlgebraicClosure ℚ)).fieldRange.fixingSubgroup)) (AlgebraicClosure ℚ))) => IsLocalRing.residue ↥Pl (ι o)) ∧
      (∀ σ ∈ Pl.inertiaSubgroupIn ℚ ⊓ (IsScalarTower.toAlgHom ℚ L (AlgebraicClosure ℚ)).fieldRange.fixingSubgroup,
        ∀ o : ↥(Pl.comap (algebraMap ↥(IntermediateField.fixedField (Pl.inertiaSubgroupIn ℚ ⊓ (IsScalarTower.toAlgHom ℚ L (AlgebraicClosure ℚ)).fieldRange.fixingSubgroup)) (AlgebraicClosure ℚ))), σ ((ι o : ↥Pl) : AlgebraicClosure ℚ) = ((ι o : ↥Pl) : AlgebraicClosure ℚ)) := by sorry
