-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_valuationSubring_lift_variableChange_veluQuotient_reduceHom_eq_of_three_smul_mem_zmultiples_of_two_eq_zero
-- name    : WeierstrassCurve.exists_valuationSubring_lift_variableChange_veluQuotient_reduceHom_eq_of_three_smul_mem_zmultiples_of_two_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.985064+00:00
-- url     : https://prove2.me/theorems/6bc3075c-c794-5656-bea3-ee5872aff373
-- title:
--   Deuring lifting in residue characteristic two, three-torsion form
-- statement:
--   Let $p$ be a prime, $k$ an algebraically closed field of characteristic $p$ with decidable equality in which $2=0$, and $W$ an elliptic Weierstrass curve over $k$. Fix $n$ with $2n+1\neq 0$ in $k$ and $2n+1$ not a square, a point $Q_0$ of $W$ of exact additive order $2n+1$, and a Weierstrass variable change $\gamma_0$ over $k$ with $\gamma_0\cdot W = W/S_0$, where $S_0=W.\mathrm{oddOrderSummingSet}\,Q_0\,n$ is the finset of coordinate pairs of $jQ_0$ for $1\le j\le n$ (the point at infinity contributing $(0,0)$) and $W/S_0$ is the curve with the same $a_1,a_2,a_3$ and with $a_4,a_6$ corrected by the Vélu sums. Let $\Omega$ be an algebraically closed field of characteristic $0$, algebraic over the fraction field of $\mathbb{W}(k)$. Then there are: a valuation subring $B\subseteq\Omega$, a ring isomorphism $\varphi$ of $k$ with the residue field of $B$, an elliptic curve $E'$ over $B$ whose reduction has $\Delta\neq 0$, a variable change $v'$ over the residue field with $v'\cdot(E'\bmod\mathfrak m)=W\otimes_\varphi$, a point $Q'$ of $E'$ over $\Omega$ of exact order $2n+1$ whose reduction corresponds to $\varphi_*Q_0$, and a variable change $\gamma$ over $\Omega$ with $\gamma\cdot E'_\Omega=E'_\Omega/S'$, $S'$ the analogous summing set of $Q'$, such that for all affine nonsingular $(x',y')$ on $E'_\Omega$ and $(x,y)$ on $W$ with $3P\in\langle Q_0\rangle$, $P\notin\langle Q_0\rangle$, $3P'\in\langle Q'\rangle$ and $P'$ reducing to $\varphi_*P$, the Vélu images $(\mathrm{veluX},\mathrm{veluY})$ of $(x,y)$ and of $(x',y')$ are nonsingular on the respective quotients and, transported to $W$ and to $E'_\Omega$ by $\gamma_0$ and $\gamma$, again correspond under $\varphi$ and reduction.
--
--   This is the deformation-theoretic core of Deuring's lifting theorem in residue characteristic $2$, in the form that lifts simultaneously the curve, a point of odd order $2n+1$, and the self-isogeny with kernel $\langle Q_0\rangle$ realised as a Vélu quotient, the compatibility being tested on points $P$ with $3P\in\langle Q_0\rangle$ but $P\notin\langle Q_0\rangle$. It feeds the construction of a valuation subring together with an identification of residue fields compatible with reduction of points, used in the characteristic-$2$ case of the lifting of elliptic curves with prescribed endomorphism.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_valuationSubring_lift_variableChange_veluQuotient_reduceHom_eq_of_three_smul_mem_zmultiples_of_two_eq_zero.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_ReduceHom
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Definitions.Def_WeierstrassCurve_RatPointHom
import Definitions.Def_WeierstrassCurve_Velu
import Definitions.Def_WeierstrassCurve_VeluQuotientMap
import Definitions.Def_WeierstrassCurve_VeluPointMap
import Definitions.Def_WeierstrassCurve_OddOrderSummingSet

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped Classical in

theorem WeierstrassCurve.exists_valuationSubring_lift_variableChange_veluQuotient_reduceHom_eq_of_three_smul_mem_zmultiples_of_two_eq_zero
    (p : ℕ) [Fact p.Prime] {k : Type} [Field k] [IsAlgClosed k] [CharP k p] [DecidableEq k]
    (h2 : (2 : k) = 0)
    (W : WeierstrassCurve k) [W.IsElliptic] (n : ℕ) (hm : ((2 * n + 1 : ℕ) : k) ≠ 0)
    (hsq : ¬ IsSquare (2 * n + 1)) (Q₀ : W.toAffine.Point) (hQ₀ : addOrderOf Q₀ = 2 * n + 1)
    (γ₀ : WeierstrassCurve.VariableChange k)
    (hγ₀ : γ₀ • W = W.veluQuotient (W.oddOrderSummingSet Q₀ n))
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [CharZero Ω] [Algebra (FractionRing (WittVector p k)) Ω]
    [Algebra.IsAlgebraic (FractionRing (WittVector p k)) Ω] :
    ∃ (B : ValuationSubring Ω) (φ : k ≃+* IsLocalRing.ResidueField B) (E' : WeierstrassCurve B)
      (_ : E'.IsElliptic) (hΔ' : (E'.map (IsLocalRing.residue B)).Δ ≠ 0)
      (v' : WeierstrassCurve.VariableChange (IsLocalRing.ResidueField B))
      (hv' : v' • E'.map (IsLocalRing.residue B) = W.map φ.toRingHom)
      (Q' : (E'.map B.subtype).toAffine.Point) (_ : addOrderOf Q' = 2 * n + 1)
      (_ : WeierstrassCurve.ratPointHom φ.toRingHom Q₀ =
        (WeierstrassCurve.Affine.Point.equivOfVariableChangeEq hv').symm
          (WeierstrassCurve.reduceHom hΔ' Q'))
      (γ : WeierstrassCurve.VariableChange Ω)
      (hγ : γ • E'.map B.subtype =
        (E'.map B.subtype).veluQuotient ((E'.map B.subtype).oddOrderSummingSet Q' n)),
      ∀ (x' y' : Ω) (h' : (E'.map B.subtype).toAffine.Nonsingular x' y')
        (x y : k) (h : W.toAffine.Nonsingular x y),
        (3 : ℤ) • (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point)
          ∈ AddSubgroup.zmultiples Q₀ →
        (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point) ∉ AddSubgroup.zmultiples Q₀ →
        (3 : ℤ) • (WeierstrassCurve.Affine.Point.some x' y' h' : (E'.map B.subtype).toAffine.Point)
          ∈ AddSubgroup.zmultiples Q' →
        WeierstrassCurve.ratPointHom φ.toRingHom (.some x y h) =
          (WeierstrassCurve.Affine.Point.equivOfVariableChangeEq hv').symm
            (WeierstrassCurve.reduceHom hΔ' (.some x' y' h')) →
        ∃ (h'' : ((E'.map B.subtype).veluQuotient
              ((E'.map B.subtype).oddOrderSummingSet Q' n)).toAffine.Nonsingular
              ((E'.map B.subtype).veluX ((E'.map B.subtype).oddOrderSummingSet Q' n) x')
              ((E'.map B.subtype).veluY ((E'.map B.subtype).oddOrderSummingSet Q' n) x' y'))
          (h₀'' : (W.veluQuotient (W.oddOrderSummingSet Q₀ n)).toAffine.Nonsingular
              (W.veluX (W.oddOrderSummingSet Q₀ n) x) (W.veluY (W.oddOrderSummingSet Q₀ n) x y)),
          WeierstrassCurve.ratPointHom φ.toRingHom
              (WeierstrassCurve.Affine.Point.equivOfVariableChangeEq hγ₀ (.some _ _ h₀'')) =
            (WeierstrassCurve.Affine.Point.equivOfVariableChangeEq hv').symm
              (WeierstrassCurve.reduceHom hΔ'
                (WeierstrassCurve.Affine.Point.equivOfVariableChangeEq hγ (.some _ _ h''))) := by sorry
