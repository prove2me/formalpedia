-- Prove2me | Theorems.Thm_TateCurve_exists_finiteFlat_prolongation_torsion_padicInt_of_dvd_valuation_of_five_le
-- name    : TateCurve.exists_finiteFlat_prolongation_torsion_padicInt_of_dvd_valuation_of_five_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.134728+00:00
-- url     : https://prove2.me/theorems/dc77e459-f222-564a-bfe9-5e2ead9454c2
-- title:
--   Finite flat prolongation of Tate-curve p-torsion, p ≥ 5
-- statement:
--   Let $p$ be a prime with $5 \le p$, and let $q \in \mathbb{Q}_p$ be non-zero with $\|q\|_{\mathbb{N}\mathbb{R}_{\ge 0}} < 1$ and such that $p$ divides the $p$-adic valuation of $q$ as an integer. Then there exist a type $H$, a commutative ring structure on it and a Hopf algebra structure over $\mathbb{Z}_p$, such that $H$ is finite as a $\mathbb{Z}_p$-module, flat over $\mathbb{Z}_p$, and its comultiplication is cocommutative, together with a bijection $e$ from `WithConv (H →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p])`, the set of $\mathbb{Z}_p$-algebra homomorphisms $H \to \overline{\mathbb{Q}_p}$ carried by the convolution multiplication, onto the $p$-torsion submodule `Submodule.torsionBy ℤ … p` of the group of points of the Weierstrass curve [`TateCurve.curve q`](def/TateCurve_QSeries.html#L185), that is $\langle 1, 0, 0, a_4(q), a_6(q)\rangle$ with the Tate $q$-series coefficients, base changed to $\overline{\mathbb{Q}_p}$. The bijection satisfies $e(f \cdot g) = e(f) + e(g)$ for all $f, g$, and is Galois-equivariant in the following form: for every $\mathbb{Q}_p$-algebra automorphism $\sigma$ of $\overline{\mathbb{Q}_p}$ and all $f, g$ with $g(h) = \sigma(f(h))$ for all $h \in H$, one has $e(g) = \sigma \cdot e(f)$.
--
--   This is the $p \ge 5$ case of the statement that the $p$-torsion of a Tate curve over $\mathbb{Q}_p$ whose parameter has valuation divisible by $p$ prolongs to a finite flat commutative group scheme over $\mathbb{Z}_p$, presented here as a finite flat cocommutative Hopf algebra $H$ over $\mathbb{Z}_p$ whose $\overline{\mathbb{Q}_p}$-points, with their convolution group law and Galois action, are identified with $E_q[p](\overline{\mathbb{Q}_p})$. It feeds the unconditional statement [`TateCurve.exists_finiteFlat_prolongation_torsion_padicInt_of_dvd_valuation`](thm.html#TateCurve.exists_finiteFlat_prolongation_torsion_padicInt_of_dvd_valuation), which is used in the finite-flatness analysis at $p$ of the Galois representations attached to the Frey curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_TateCurve_exists_finiteFlat_prolongation_torsion_padicInt_of_dvd_valuation_of_five_le.lean

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

theorem TateCurve.exists_finiteFlat_prolongation_torsion_padicInt_of_dvd_valuation_of_five_le
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (qT : ℚ_[p]) (hqT0 : qT ≠ 0) (hqT1 : ‖qT‖₊ < 1)
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
