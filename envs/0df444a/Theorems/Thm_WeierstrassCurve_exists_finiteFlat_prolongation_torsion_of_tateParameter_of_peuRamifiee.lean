-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_finiteFlat_prolongation_torsion_of_tateParameter_of_peuRamifiee
-- name    : WeierstrassCurve.exists_finiteFlat_prolongation_torsion_of_tateParameter_of_peuRamifiee
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.681435+00:00
-- url     : https://prove2.me/theorems/a2e082ae-8853-5865-ba1d-7b478cd61005
-- title:
--   Finite flat prolongation of E[p] from a Tate parameter
-- statement:
--   Let $E$ be a Weierstrass curve over $\mathbb{Q}$ and $W$ a Weierstrass curve over $\mathbb{Z}$ which is an integral model of $E$ in the sense that some variable change over $\mathbb{Q}$ carries $E$ to the base change of $W$ along $\mathbb{Z} \to \mathbb{Q}$. Let $p$ be a prime, and assume $\Delta_W \neq 0$, $p \mid \Delta_W$, $p \nmid c_4(W)$ and $p \mid v_p(\Delta_W)$ (the last being the peu-ramifiée condition, with $v_p$ the $p$-adic valuation of an integer). Assume given $q_T \in \mathbb{Q}_p$ with $q_T \neq 0$ and $\|q_T\| < 1$, such that the Weierstrass curve $\langle 1,0,0,a_4(q_T),a_6(q_T)\rangle$ attached to $q_T$ satisfies $c_4^3 = j \cdot \Delta$, where $j$ is the image in $\mathbb{Q}_p$ of the rational number $c_4(W_{\mathbb{Q}})^3/\Delta(W_{\mathbb{Q}})$, and such that $\|q_T\| = p^{-v_p(\Delta_W)}$. Write $R$ for the subring of $\mathbb{Q}$ consisting of rationals whose denominator is coprime to $p$. The conclusion asserts the existence of a type $H$ with a commutative ring structure and a Hopf algebra structure over $R$ which is finite and flat as an $R$-module and cocommutative as a coalgebra, together with a bijection $e$ from the convolution monoid $\mathrm{WithConv}$ of $R$-algebra homomorphisms $H \to \overline{\mathbb{Q}}$ onto the $p$-torsion submodule of the group of points of $E$ over $\overline{\mathbb{Q}}$, such that $e(fg) = e(f) + e(g)$ for all $f,g$, and such that for every $\sigma \in \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ and all $f,g$ with $g(h) = \sigma(f(h))$ for every $h \in H$ one has $e(g) = \sigma \cdot e(f)$.
--
--   This is the forward implication of Serre's criterion (Duke Math. J. 54 (1987), §2.8, Proposition 4) at a prime of multiplicative reduction: when the $p$-adic valuation of the discriminant is divisible by $p$, the Galois module $E[p]$ is the group of $\overline{\mathbb{Q}}$-points of a finite flat commutative group scheme over $\mathbb{Z}_{(p)}$, presented here through its Hopf algebra. It is the remaining input to the corresponding statement phrased in terms of multiplicative reduction, which it supplies once a Tate parameter has been produced.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_finiteFlat_prolongation_torsion_of_tateParameter_of_peuRamifiee.lean

import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_TateCurve_TateParameter

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped NNReal
open scoped WeierstrassCurve.Affine in
open WeierstrassCurve WeierstrassCurve.Affine.Point in

theorem WeierstrassCurve.exists_finiteFlat_prolongation_torsion_of_tateParameter_of_peuRamifiee
    (E : WeierstrassCurve ℚ) {W : WeierstrassCurve ℤ} (hW : W.IsIntegralModelOf E)
    (p : ℕ) [Fact p.Prime] (hΔ : W.Δ ≠ 0)
    (hpΔ : (p : ℤ) ∣ W.Δ) (hpc₄ : ¬ (p : ℤ) ∣ W.c₄)
    (hpr : p ∣ padicValInt p W.Δ)
    (qT : ℚ_[p]) (hqT0 : qT ≠ 0) (hqT1 : ‖qT‖₊ < 1)
    (hj : (TateCurve.curve qT).c₄ ^ 3
        = (((W.map (Int.castRingHom ℚ)).c₄ ^ 3 / (W.map (Int.castRingHom ℚ)).Δ : ℚ) : ℚ_[p])
            * (TateCurve.curve qT).Δ)
    (hv : ‖qT‖₊ = ((p : ℝ≥0) ^ padicValInt p W.Δ)⁻¹) :
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
