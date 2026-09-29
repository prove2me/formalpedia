-- Prove2me | Theorems.Thm_WeierstrassCurve_isOpen_torsionBy_fixingSubgroup
-- name    : WeierstrassCurve.isOpen_torsionBy_fixingSubgroup
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.985064+00:00
-- url     : https://prove2.me/theorems/488edafc-4687-54b2-b4c1-7670494d9570
-- title:
--   Openness of the pointwise stabiliser of n-torsion
-- statement:
--   Let $W$ be a Weierstrass curve over $\mathbb{Z}$, let $n$ be a natural number, and assume that the discriminant $W.\Delta$ is non-zero and that $n > 0$. Write $E$ for the base change of $W$ along $\mathbb{Z} \to \mathbb{Q}$, viewed over the algebraic closure $\overline{\mathbb{Q}}$ of $\mathbb{Q}$, and let $E(\overline{\mathbb{Q}})$ be its group of affine points together with the point at infinity. The assertion is that the set of those $\mathbb{Q}$-algebra automorphisms $\sigma$ of $\overline{\mathbb{Q}}$ such that $\sigma \cdot x = x$ for every element $x$ of the $\mathbb{Z}$-submodule of $E(\overline{\mathbb{Q}})$ annihilated by $n$ — i.e. for every $n$-torsion point — is open in $\mathrm{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})$ with its Krull topology. The statement is about a set, not a subgroup: openness of the underlying set of the pointwise stabiliser of $E[n]$ is what is asserted.
--
--   This is the standard statement that the Galois representation on $E[n]$ is continuous, in the form that the kernel of the action on $E[n]$ is an open subset of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$; it supplies the openness input required before arithmetic statements about open subgroups (such as Minkowski-type or inertia arguments) can be applied to the action on torsion. It is used in the construction of Galois-stable cyclic subgroups of $p$-power order for the Frey curve ([`AddSubgroup.exists_towerStep_of_extVanishingCts`](thm.html#AddSubgroup.exists_towerStep_of_extVanishingCts), [`FreyPackage.frey_no_cofixed_large`](thm.html#FreyPackage.frey_no_cofixed_large)) and in [`WeierstrassCurve.not_forall_apOfModel_eq_two_of_modRepIsIrreducible`](thm.html#WeierstrassCurve.not_forall_apOfModel_eq_two_of_modRepIsIrreducible).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_isOpen_torsionBy_fixingSubgroup.lean

import Mathlib
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem WeierstrassCurve.isOpen_torsionBy_fixingSubgroup
    (W : WeierstrassCurve ℤ) (n : ℕ) (hΔ : W.Δ ≠ 0) (hn : 0 < n) :
    IsOpen {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ |
      ∀ x : Submodule.torsionBy ℤ
        ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point (n : ℤ), σ • x = x} := by sorry
