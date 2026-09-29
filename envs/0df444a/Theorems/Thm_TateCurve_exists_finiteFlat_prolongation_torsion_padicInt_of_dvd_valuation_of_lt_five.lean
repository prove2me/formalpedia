-- Prove2me | Theorems.Thm_TateCurve_exists_finiteFlat_prolongation_torsion_padicInt_of_dvd_valuation_of_lt_five
-- name    : TateCurve.exists_finiteFlat_prolongation_torsion_padicInt_of_dvd_valuation_of_lt_five
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.134728+00:00
-- url     : https://prove2.me/theorems/3fec6cac-2221-584a-aeb5-a3028c256663
-- title:
--   Finite flat prolongation of E_q[p] for p<5
-- statement:
--   Let $p$ be a prime with $p<5$, and let $qT\in\mathbb{Q}_p$ be nonzero with $\|qT\|<1$ and with $p$ dividing the $p$-adic valuation $\mathrm{Padic.valuation}\,qT\in\mathbb{Z}$. Write $E_{qT}$ for the Tate curve [`TateCurve.curve qT`](def/TateCurve_QSeries.html#L185), i.e. the Weierstrass curve over $\mathbb{Q}_p$ with coefficients $a_1=1$, $a_2=a_3=0$ and $a_4,a_6$ the $q$-series values `a₄ qT`, `a₆ qT`. The assertion is that there is a type $H$ carrying a commutative ring structure and a Hopf algebra structure over $\mathbb{Z}_p$, such that $H$ is finite and flat as a $\mathbb{Z}_p$-module, its comultiplication is cocommutative, and there is a bijection $e$ from the type of $\mathbb{Z}_p$-algebra homomorphisms $H\to\overline{\mathbb{Q}_p}$, equipped with its convolution multiplication (`WithConv`), onto the $p$-torsion submodule $\{P : pP=0\}$ of the group of affine points of the base change of $E_{qT}$ to an algebraic closure $\overline{\mathbb{Q}_p}$, with the two compatibilities: $e(f\cdot g)=e(f)+e(g)$ for all $f,g$, and, for every $\mathbb{Q}_p$-algebra automorphism $\sigma$ of $\overline{\mathbb{Q}_p}$ and all $f,g$ with $g(h)=\sigma(f(h))$ for all $h\in H$, the relation $e(g)=\sigma\cdot e(f)$ for the Galois action on points.
--
--   This is the small-prime instance of the statement that, when $p\mid v_p(q)$, the $p$-torsion of the Tate curve $E_q$ over $\mathbb{Q}_p$ extends to a finite flat commutative group scheme over $\mathbb{Z}_p$, the group scheme being presented by its Hopf algebra $H$ together with a Galois-equivariant identification of its $\overline{\mathbb{Q}_p}$-points with $E_q[p]$. It feeds the unconditional form [`TateCurve.exists_finiteFlat_prolongation_torsion_padicInt_of_dvd_valuation`](thm.html#TateCurve.exists_finiteFlat_prolongation_torsion_padicInt_of_dvd_valuation), whose other branch treats $p\ge 5$ by the explicit Tate parametrisation of torsion points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_TateCurve_exists_finiteFlat_prolongation_torsion_padicInt_of_dvd_valuation_of_lt_five.lean

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

theorem TateCurve.exists_finiteFlat_prolongation_torsion_padicInt_of_dvd_valuation_of_lt_five
    (p : ℕ) [Fact p.Prime] (hp5 : p < 5) (qT : ℚ_[p]) (hqT0 : qT ≠ 0) (hqT1 : ‖qT‖₊ < 1)
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
