-- Prove2me | Theorems.Thm_TateCurve_exists_finiteFlat_prolongation_torsion_padicInt_of_dvd_valuation
-- name    : TateCurve.exists_finiteFlat_prolongation_torsion_padicInt_of_dvd_valuation
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.134728+00:00
-- url     : https://prove2.me/theorems/451f35c5-10bf-566f-b647-591d1877f331
-- title:
--   p-torsion of a Tate curve prolongs when p ∣ vₚ(q)
-- statement:
--   Let $p$ be a prime and let $qT \in \mathbb{Q}_p$ be non-zero with $\|qT\| < 1$ and with $p$ dividing the $p$-adic valuation of $qT$ (as integers). Then there exist a type $H$ (in the lowest universe) carrying a commutative ring structure and a Hopf algebra structure over $\mathbb{Z}_p$ such that $H$ is finite as a $\mathbb{Z}_p$-module, flat as a $\mathbb{Z}_p$-module, and cocommutative as a $\mathbb{Z}_p$-coalgebra, together with a bijection $e$ from `WithConv` of the set of $\mathbb{Z}_p$-algebra homomorphisms $H \to \overline{\mathbb{Q}_p}$ — that is, this set of homomorphisms equipped with its convolution multiplication — onto the $p$-torsion submodule $\mathrm{torsionBy}\ \mathbb{Z}\ \cdot\ p$ of the group of points of the affine Weierstrass curve $\mathrm{TateCurve.curve}\ qT$, given by the coefficients $a_1 = 1$, $a_2 = a_3 = 0$ and the $q$-series coefficients $a_4(qT)$, $a_6(qT)$, base-changed to $\overline{\mathbb{Q}_p}$; the bijection $e$ carries the convolution product to addition of points, $e(f \cdot g) = e(f) + e(g)$, and is Galois-equivariant in the form: for every $\sigma \in \mathrm{Gal}(\overline{\mathbb{Q}_p}/\mathbb{Q}_p)$ and all $f, g$ with $g(h) = \sigma(f(h))$ for all $h \in H$, one has $e(g) = \sigma \cdot e(f)$.
--
--   This is the Tate-curve case of the prolongation statement underlying Serre's "peu ramifiée" condition: when the Tate parameter has valuation divisible by $p$, the $p$-torsion of $E_q = \mathbb{G}_m/q^{\mathbb{Z}}$ is, as a Galois module, the group of $\overline{\mathbb{Q}_p}$-points of a finite flat commutative group scheme over $\mathbb{Z}_p$, presented here through its Hopf algebra. It feeds the corresponding assertion for an elliptic curve with multiplicative reduction and a peu ramifiée Tate parameter, [`WeierstrassCurve.exists_finiteFlat_prolongation_torsion_padicInt_of_tateParameter_of_peuRamifiee`](thm.html#WeierstrassCurve.exists_finiteFlat_prolongation_torsion_padicInt_of_tateParameter_of_peuRamifiee).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_TateCurve_exists_finiteFlat_prolongation_torsion_padicInt_of_dvd_valuation.lean

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_TateCurve_TateParameter
import Definitions.Def_TateCurve_TorsionParametrization
import Definitions.Def_FLTPrelim_GaloisRep

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped NNReal
open scoped WeierstrassCurve.Affine in
open WeierstrassCurve WeierstrassCurve.Affine.Point in

theorem TateCurve.exists_finiteFlat_prolongation_torsion_padicInt_of_dvd_valuation
    (p : ℕ) [Fact p.Prime] (qT : ℚ_[p]) (hqT0 : qT ≠ 0) (hqT1 : ‖qT‖₊ < 1)
    (hpr : (p : ℤ) ∣ Padic.valuation qT) :
    letI : DecidableEq (AlgebraicClosure ℚ_[p]) := Classical.decEq _
    ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra ℤ_[p] H),
      Module.Finite ℤ_[p] H ∧
      Module.Flat ℤ_[p] H ∧
      Coalgebra.IsCocomm ℤ_[p] H ∧
      ∃ e : WithConv (H →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p]) ≃
          Submodule.torsionBy ℤ ((TateCurve.curve qT)⁄(AlgebraicClosure ℚ_[p])).Point p,
        (∀ f g, e (f * g) = e f + e g) ∧
        ∀ (σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])
          (f g : WithConv (H →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p])),
          (∀ h : H, g h = σ (f h)) → e g = σ • (e f) := by sorry
