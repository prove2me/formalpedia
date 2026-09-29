-- Prove2me | Theorems.Thm_WeierstrassCurve_bijective_torsionBy_pointMap_ratAlgClosure_padicAlgClosure_of_isElliptic
-- name    : WeierstrassCurve.bijective_torsionBy_pointMap_ratAlgClosure_padicAlgClosure_of_isElliptic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/12dcb644-48a3-5948-86d2-54d01fcb80c1
-- title:
--   Bijectivity of E[p](ℚ̄)→ E[p](mathbb Qₚ̄), elliptic case
-- statement:
--   Let $E$ be a Weierstrass curve over $\mathbb Q$ which is elliptic (its discriminant is a unit, in the sense of the `IsElliptic` class), let $p$ be a prime number, and let $\iota$ be a $\mathbb Q$-algebra homomorphism from $\mathrm{AlgebraicClosure}\ \mathbb Q$ to $\mathrm{AlgebraicClosure}\ \mathbb Q_{[p]}$. Write $E\!\!\;⁄L$ for the base change of $E$ to an affine Weierstrass curve over $L$ and $(E⁄L).\mathrm{Point}$ for its group of affine points together with the point at infinity, regarded as a $\mathbb Z$-module. Inside this group consider the submodule $\mathrm{Submodule.torsionBy}\ \mathbb Z\ \_\ p$ of points killed by $(p:\mathbb Z)$, i.e. the $p$-torsion. The coordinatewise map `WeierstrassCurve.Affine.Point.map` along $\iota$ sends a $p$-torsion point of $(E⁄\mathrm{AlgebraicClosure}\ \mathbb Q).\mathrm{Point}$ to a $p$-torsion point of $(E⁄\mathrm{AlgebraicClosure}\ \mathbb Q_{[p]}).\mathrm{Point}$, since it is an additive homomorphism; the assertion is that the resulting function between the two $p$-torsion submodules is bijective.
--
--   This identifies the $p$-torsion of an elliptic curve over $\mathbb Q$ computed over an algebraic closure of $\mathbb Q$ with the one computed over an algebraic closure of $\mathbb Q_p$, compatibly with a chosen embedding $\iota$; it is the elliptic branch of [`WeierstrassCurve.bijective_torsionBy_pointMap_ratAlgClosure_padicAlgClosure`](thm.html#WeierstrassCurve.bijective_torsionBy_pointMap_ratAlgClosure_padicAlgClosure), which cites it alongside the companion statement for curves that are not elliptic. Such a comparison is what allows the mod $p$ representation attached to $E$ to be studied locally at $p$ without changing the underlying torsion module.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_bijective_torsionBy_pointMap_ratAlgClosure_padicAlgClosure_of_isElliptic.lean

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_FLTPrelim_GaloisRep

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped NNReal
open scoped WeierstrassCurve.Affine in
open WeierstrassCurve WeierstrassCurve.Affine.Point in

theorem WeierstrassCurve.bijective_torsionBy_pointMap_ratAlgClosure_padicAlgClosure_of_isElliptic
    (E : WeierstrassCurve ℚ) [E.IsElliptic] (p : ℕ) [Fact p.Prime]
    (ι : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ_[p]) :
    letI : DecidableEq (AlgebraicClosure ℚ) := Classical.decEq _
    letI : DecidableEq (AlgebraicClosure ℚ_[p]) := Classical.decEq _
    Function.Bijective
      (fun P : Submodule.torsionBy ℤ (E⁄(AlgebraicClosure ℚ)).Point p =>
        (⟨WeierstrassCurve.Affine.Point.map ι (P : (E⁄(AlgebraicClosure ℚ)).Point), by
          have hP := (Submodule.mem_torsionBy_iff _ _).mp P.property
          rw [Submodule.mem_torsionBy_iff, ← map_zsmul, hP]
          exact _root_.map_zero _⟩ :
        Submodule.torsionBy ℤ (E⁄(AlgebraicClosure ℚ_[p])).Point p)) := by sorry
