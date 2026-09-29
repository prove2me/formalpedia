-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_valuationSubring_lift_variableChange_veluQuotient_reduceHom_eq_of_two_smul_mem_zmultiples
-- name    : WeierstrassCurve.exists_valuationSubring_lift_variableChange_veluQuotient_reduceHom_eq_of_two_smul_mem_zmultiples
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.985064+00:00
-- url     : https://prove2.me/theorems/158618cf-638e-52c5-9cb7-b061693d3f67
-- title:
--   Deuring lift compatible with Vélu quotient on two-torsion test points
-- statement:
--   Fix a prime $p$ and an algebraically closed field $k$ of characteristic $p$ with decidable equality in which $2 \neq 0$, an elliptic Weierstrass curve $W/k$, and $n \in \mathbb{N}$ such that $2n+1 \neq 0$ in $k$ and $2n+1$ is not a square. Let $Q_0 \in W(k)$ have exact additive order $2n+1$, and let $\gamma_0$ be a change of Weierstrass coordinates over $k$ with $\gamma_0 \cdot W$ equal to the Vélu quotient of $W$ by the finite set `W.oddOrderSummingSet Q₀ n` of coordinate pairs of $Q_0, 2Q_0, \dots, nQ_0$ (the curve with the same $a_1,a_2,a_3$ and $a_4,a_6$ corrected by the Vélu sums). Let $\Omega$ be an algebraically closed field of characteristic $0$, algebraic over the fraction field of the Witt vectors $\mathbb{W}(k)$. Then there are: a valuation subring $B \subseteq \Omega$; a ring isomorphism $\varphi$ of $k$ with the residue field of $B$; an elliptic curve $E'/B$ whose reduction $E' \bmod \mathfrak{m}_B$ has nonzero discriminant, together with a coordinate change $v'$ over the residue field carrying that reduction to $W$ transported along $\varphi$; a point $Q'$ of $E'_\Omega = E'\!\otimes\! \Omega$ of exact order $2n+1$ whose reduction, transported by $v'$, is the coordinatewise image $\varphi_*(Q_0)$; and a coordinate change $\gamma$ over $\Omega$ with $\gamma \cdot E'_\Omega$ the Vélu quotient of $E'_\Omega$ by `oddOrderSummingSet Q' n`; such that for all affine nonsingular points $P' = (x',y')$ on $E'_\Omega$ and $P = (x,y)$ on $W$ with $2P \in \langle Q_0 \rangle$, $P \notin \langle Q_0 \rangle$, $2P' \in \langle Q' \rangle$, and $\varphi_*(P)$ equal to the $v'$-transported reduction of $P'$, the Vélu images $(\mathrm{veluX}, \mathrm{veluY})$ of $P'$ and of $P$ are nonsingular on the respective quotient curves, and $\varphi_*$ of the $\gamma_0$-transport of the Vélu image of $P$ coincides with the $v'$-transported reduction of the $\gamma$-transport of the Vélu image of $P'$. Here the reduction map sends points whose $x$-coordinate lies outside $B$ to the point at infinity, and $\varphi_*$ acts coordinatewise.
--
--   This is the deformation-theoretic core of Deuring's lifting theorem in the shape needed for Vélu quotients: an elliptic curve over $k$ admitting an isomorphism with a cyclic quotient of odd degree $2n+1$ is lifted, together with the generator of the kernel and the quotient isomorphism, to a curve over a valuation subring of a characteristic-zero field, the compatibility being tested on points whose double lies in the cyclic kernel. It feeds the construction of a lift of the corresponding endomorphism in [`WeierstrassCurve.exists_valuationSubring_residueField_equiv_and_reduceHom_comp_eq_of_isAlgClosed_of_comp_self_add_smul_eq_smul`](thm.html#WeierstrassCurve.exists_valuationSubring_residueField_equiv_and_reduceHom_comp_eq_of_isAlgClosed_of_comp_self_add_smul_eq_smul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_valuationSubring_lift_variableChange_veluQuotient_reduceHom_eq_of_two_smul_mem_zmultiples.lean

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

theorem WeierstrassCurve.exists_valuationSubring_lift_variableChange_veluQuotient_reduceHom_eq_of_two_smul_mem_zmultiples
    (p : ℕ) [Fact p.Prime] {k : Type} [Field k] [IsAlgClosed k] [CharP k p] [DecidableEq k]
    (h2 : (2 : k) ≠ 0)
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
        (2 : ℤ) • (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point)
          ∈ AddSubgroup.zmultiples Q₀ →
        (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point) ∉ AddSubgroup.zmultiples Q₀ →
        (2 : ℤ) • (WeierstrassCurve.Affine.Point.some x' y' h' : (E'.map B.subtype).toAffine.Point)
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
