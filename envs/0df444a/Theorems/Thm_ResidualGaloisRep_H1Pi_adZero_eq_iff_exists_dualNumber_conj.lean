-- Prove2me | Theorems.Thm_ResidualGaloisRep_H1Pi_adZero_eq_iff_exists_dualNumber_conj
-- name    : ResidualGaloisRep.H1Pi_adZero_eq_iff_exists_dualNumber_conj
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:01.535489+00:00
-- url     : https://prove2.me/theorems/2e4f4aba-aaa4-547c-a5aa-3f46aaa3a895
-- title:
--   Equality of H¹(ℚ,ad⁰ρ̄) classes versus strict conjugacy of dual lifts
-- statement:
--   Let $k$ be a field in which $2$ is a unit, and let $\bar\rho$ be a residual Galois representation over $k$: a $k$-vector space $V$ with $\dim_k V = 2$ together with a monoid homomorphism $\bar\rho : \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q}) \to \operatorname{End}_k V$ (the absolute Galois group being realised as $\overline{\mathbb{Q}} \simeq_{\mathbb{Q}} \overline{\mathbb{Q}}$ for $\overline{\mathbb{Q}}$ an algebraic closure of $\mathbb{Q}$) which factors through a finite level, i.e. there is an intermediate field $L$ of $\overline{\mathbb{Q}}/\mathbb{Q}$ with $L/\mathbb{Q}$ finite such that $\bar\rho(\sigma) = 1$ whenever $\sigma$ fixes $L$ pointwise. Let $\rho, \rho'$ be group homomorphisms from the Galois group to the units of the dual-number ring $(\operatorname{End}_k V)[\varepsilon]$ which are dual lifts of the unit-valued form of $\bar\rho$, meaning that the $\varepsilon$-free component of $\rho(\sigma)$ (resp. $\rho'(\sigma)$) equals $\bar\rho(\sigma)$ for every $\sigma$. Let $c, c'$ be $1$-cocycles of the representation $\operatorname{ad}^0\bar\rho$, that is of the restriction of the adjoint (conjugation) representation on $\operatorname{End}_k V$ to the kernel of the trace, and assume that the endomorphism underlying $c(\sigma)$ is $(\rho(\sigma))_{\varepsilon} \,\bar\rho(\sigma)^{-1}$ and that underlying $c'(\sigma)$ is $(\rho'(\sigma))_{\varepsilon}\,\bar\rho(\sigma)^{-1}$, for all $\sigma$, where $(\cdot)_{\varepsilon}$ denotes the $\varepsilon$-component. Then $c$ and $c'$ have the same class in $H^1$ of $\operatorname{ad}^0\bar\rho$ if and only if there is a unit $w$ of $(\operatorname{End}_k V)[\varepsilon]$ whose $\varepsilon$-free component is $1$ with $\rho'(\sigma) = w\,\rho(\sigma)\,w^{-1}$ for all $\sigma$.
--
--   This identifies the tangent space of the deformation problem with fixed determinant: strict equivalence classes of dual-number lifts of $\bar\rho$ whose associated cochains take trace-zero values correspond bijectively to classes in $H^1(\mathbb{Q}, \operatorname{ad}^0\bar\rho)$. It is used in bounding the number of generators of the maximal ideal of the deformation ring by the dimension of the space of dual-number classes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ResidualGaloisRep_H1Pi_adZero_eq_iff_exists_dualNumber_conj.lean

import Mathlib
import Definitions.Def_GaloisRep_AdZero
import Definitions.Def_GroupCohomology_TangentSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing groupCohomology TrivSqZeroExt
open scoped DualNumber

theorem ResidualGaloisRep.H1Pi_adZero_eq_iff_exists_dualNumber_conj
    (k : Type) [Field k] (ρbar : ResidualGaloisRep k) (h2 : IsUnit (2 : k))
    (ρ ρ' : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* (DualNumber (Module.End k ρbar.V))ˣ)
    (hρ : IsDualLift ρbar.ρ.toHomUnits ρ) (hρ' : IsDualLift ρbar.ρ.toHomUnits ρ')
    (c c' : cocycles₁ ρbar.adZero)
    (hc : ∀ σ, ((c : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →
        ↥(LinearMap.ker (LinearMap.trace k ρbar.V))) σ : Module.End k ρbar.V) =
      dualLiftToCochain ρbar.ρ.toHomUnits ρ σ)
    (hc' : ∀ σ, ((c' : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →
        ↥(LinearMap.ker (LinearMap.trace k ρbar.V))) σ : Module.End k ρbar.V) =
      dualLiftToCochain ρbar.ρ.toHomUnits ρ' σ) :
    H1π ρbar.adZero c = H1π ρbar.adZero c' ↔
      ∃ w : (DualNumber (Module.End k ρbar.V))ˣ,
        (w : DualNumber (Module.End k ρbar.V)).fst = 1 ∧ ∀ σ, ρ' σ = w * ρ σ * w⁻¹ := by sorry
