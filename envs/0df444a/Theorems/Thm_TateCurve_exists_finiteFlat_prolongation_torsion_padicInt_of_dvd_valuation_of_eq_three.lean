-- Prove2me | Theorems.Thm_TateCurve_exists_finiteFlat_prolongation_torsion_padicInt_of_dvd_valuation_of_eq_three
-- name    : TateCurve.exists_finiteFlat_prolongation_torsion_padicInt_of_dvd_valuation_of_eq_three
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.134728+00:00
-- url     : https://prove2.me/theorems/08f37537-5199-5377-b7fa-f0b72c954996
-- title:
--   Finite flat prolongation of Tate-curve 3-torsion over ℤ₃
-- statement:
--   Let $p$ be a natural number that is prime, subject to the hypothesis $p = 3$, and let $qT \in \mathbb{Q}_p$ be nonzero with $\|qT\|_+ < 1$ and with $p$ dividing the $p$-adic valuation `Padic.valuation qT` (an integer). Fix classical decidable equality on $\overline{\mathbb{Q}_p} =$ `AlgebraicClosure ℚ_[p]`. Then there exist a type $H$, a commutative ring structure on it and a Hopf algebra structure over $\mathbb{Z}_p$, such that $H$ is a finite $\mathbb{Z}_p$-module, is flat over $\mathbb{Z}_p$, and its coalgebra structure is cocommutative, together with a bijection $e$ from `WithConv (H →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p])`, the set of $\mathbb{Z}_p$-algebra homomorphisms $H \to \overline{\mathbb{Q}_p}$ equipped with its convolution multiplication, onto the $p$-torsion submodule of the group of points of [`TateCurve.curve qT`](def/TateCurve_QSeries.html#L185) base-changed to $\overline{\mathbb{Q}_p}$ — here [`TateCurve.curve qT`](def/TateCurve_QSeries.html#L185) is the Weierstrass curve over $\mathbb{Q}_p$ with $a_1 = 1$, $a_2 = a_3 = 0$ and $a_4, a_6$ the Tate $q$-series coefficients $a_4(qT)$, $a_6(qT)$ — such that $e(fg) = e(f) + e(g)$ for all $f, g$, and such that $e$ is Galois-equivariant in the following sense: for every $\sigma \in \mathrm{Gal}(\overline{\mathbb{Q}_p}/\mathbb{Q}_p)$ and all $f, g$, if $g(h) = \sigma(f(h))$ for every $h \in H$, then $e(g) = \sigma \cdot e(f)$.
--
--   This realises the $p$-torsion of a Tate curve with $p \mid v_p(q)$ as the $\overline{\mathbb{Q}_p}$-points of a finite flat commutative group scheme over $\mathbb{Z}_p$, Galois-equivariantly — the "peu ramifiée" prolongation condition in Serre's sense — in the case $p = 3$, where $\mu_p \times \mathbb{Z}/p$ is built from an explicit Kummer Hopf algebra. It feeds the small-prime branch [`TateCurve.exists_finiteFlat_prolongation_torsion_padicInt_of_dvd_valuation_of_lt_five`](thm.html#TateCurve.exists_finiteFlat_prolongation_torsion_padicInt_of_dvd_valuation_of_lt_five) of the general prolongation statement.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_TateCurve_exists_finiteFlat_prolongation_torsion_padicInt_of_dvd_valuation_of_eq_three.lean

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

theorem TateCurve.exists_finiteFlat_prolongation_torsion_padicInt_of_dvd_valuation_of_eq_three
    (p : ℕ) [Fact p.Prime] (hp : p = 3) (qT : ℚ_[p]) (hqT0 : qT ≠ 0) (hqT1 : ‖qT‖₊ < 1)
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
