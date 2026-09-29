-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_finiteFlat_prolongation_torsion_of_multiplicativeReduction_of_peuRamifiee
-- name    : WeierstrassCurve.exists_finiteFlat_prolongation_torsion_of_multiplicativeReduction_of_peuRamifiee
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.681435+00:00
-- url     : https://prove2.me/theorems/047c5dec-c575-5047-9532-01b437b1cd2b
-- title:
--   Finite flat prolongation of E[p] at a multiplicative peu-ramifiée prime
-- statement:
--   Let $E$ be a Weierstrass curve over $\mathbb{Q}$ and $W$ a Weierstrass curve over $\mathbb{Z}$ which is an integral model of $E$, in the sense that some variable change over $\mathbb{Q}$ carries $E$ to the base change of $W$ along $\mathbb{Z} \to \mathbb{Q}$. Let $p$ be a prime, and assume $\Delta_W \neq 0$, $p \mid \Delta_W$, $p \nmid c_4(W)$ (multiplicative reduction at $p$ for this model), and $p \mid v_p(\Delta_W)$, the $p$-adic valuation of the integer $\Delta_W$ (the peu-ramifiée condition). Write $R =$ [`GaloisRep.ratLocalizedAt p`](def/GaloisRep_Flat.html#L8) for the subring of $\mathbb{Q}$ consisting of those rationals whose denominator is coprime to $p$, i.e. $\mathbb{Z}_{(p)}$. The assertion is that there is a type $H$ carrying a commutative ring structure and a Hopf algebra structure over $R$, such that $H$ is a finite and flat $R$-module and its comultiplication is cocommutative, together with a bijection $e$ from `WithConv` of the set of $R$-algebra homomorphisms $H \to \overline{\mathbb{Q}}$ (where $\overline{\mathbb{Q}}$ is `AlgebraicClosure ℚ`) onto the $p$-torsion submodule $\{P : pP = 0\}$ of the group of points of $E$ base changed to $\overline{\mathbb{Q}}$, with two compatibilities: $e(fg) = e(f) + e(g)$ for all $f, g$, so $e$ is an isomorphism of the multiplicative group of $\overline{\mathbb{Q}}$-points of the Hopf algebra onto $E[p]$; and for every $\sigma \in \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ and all $f, g$ with $g(h) = \sigma(f(h))$ for every $h \in H$, one has $e(g) = \sigma \cdot e(f)$, i.e. $e$ is Galois-equivariant.
--
--   This is the prolongation half of Serre's criterion for Tate curves: at a prime of multiplicative reduction whose minimal discriminant valuation is divisible by $p$, the Galois module $E[p]$ comes from a finite flat commutative group scheme over $\mathbb{Z}_{(p)}$, presented here in the dual Hopf-algebra form. It feeds the semistable prolongation statement [`WeierstrassCurve.exists_finiteFlat_prolongation_torsion_of_semistable_of_isPeuRamifieeAt`](thm.html#WeierstrassCurve.exists_finiteFlat_prolongation_torsion_of_semistable_of_isPeuRamifieeAt) and the lower-level torsion results [`ModularCurve.hasLowerLevelTorsion_jZero_of_isPeuRamifieeAt`](thm.html#ModularCurve.hasLowerLevelTorsion_jZero_of_isPeuRamifieeAt) and [`ModularCurve.hasLowerLevelTorsion_jZero_of_isPeuRamifieeAt_of_five_le`](thm.html#ModularCurve.hasLowerLevelTorsion_jZero_of_isPeuRamifieeAt_of_five_le) used in level lowering.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_finiteFlat_prolongation_torsion_of_multiplicativeReduction_of_peuRamifiee.lean

import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_FLTPrelim_GaloisRep

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped WeierstrassCurve.Affine in
open WeierstrassCurve WeierstrassCurve.Affine.Point in

theorem WeierstrassCurve.exists_finiteFlat_prolongation_torsion_of_multiplicativeReduction_of_peuRamifiee
    (E : WeierstrassCurve ℚ) {W : WeierstrassCurve ℤ} (hW : W.IsIntegralModelOf E)
    (p : ℕ) [Fact p.Prime] (hΔ : W.Δ ≠ 0)
    (hpΔ : (p : ℤ) ∣ W.Δ) (hpc₄ : ¬ (p : ℤ) ∣ W.c₄)
    (hpr : p ∣ padicValInt p W.Δ) :
    letI : DecidableEq (AlgebraicClosure ℚ) := Classical.decEq _
    ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra (GaloisRep.ratLocalizedAt p) H),
      Module.Finite (GaloisRep.ratLocalizedAt p) H ∧
      Module.Flat (GaloisRep.ratLocalizedAt p) H ∧
      Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) H ∧
      ∃ e : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃
          Submodule.torsionBy ℤ (E⁄(AlgebraicClosure ℚ)).Point p,
        (∀ f g, e (f * g) = e f + e g) ∧
        ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
          (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
          (∀ h : H, g h = σ (f h)) → e g = σ • (e f) := by sorry
