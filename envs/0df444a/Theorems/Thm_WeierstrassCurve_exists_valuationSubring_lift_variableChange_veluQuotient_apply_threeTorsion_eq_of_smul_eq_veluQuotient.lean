-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_valuationSubring_lift_variableChange_veluQuotient_apply_threeTorsion_eq_of_smul_eq_veluQuotient
-- name    : WeierstrassCurve.exists_valuationSubring_lift_variableChange_veluQuotient_apply_threeTorsion_eq_of_smul_eq_veluQuotient
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.985064+00:00
-- url     : https://prove2.me/theorems/7755abfc-bb4a-53d2-a4c6-c78c6cf9b13e
-- title:
--   Deuring lift with level-three marking and Vélu quotient
-- statement:
--   Let $p$ be a prime and $k$ an algebraically closed field of characteristic $p$ with $3 \neq 0$, let $W$ be an elliptic Weierstrass curve over $k$, and let $n$ be a natural number such that $2n+1 \neq 0$ in $k$ and $2n+1$ is not a square. Let $Q_0$ be an affine point of $W$ of exact additive order $2n+1$, and let $\gamma_0$ be a Weierstrass variable change over $k$ with $\gamma_0 \cdot W$ equal to the Vélu quotient $W/S_0$, where $S_0 =$ `W.oddOrderSummingSet Q₀ n` is the finite set of coordinate pairs of $kQ_0$ for $1 \le k \le n$ (the point at infinity contributing $(0,0)$), and the Vélu quotient keeps $a_1,a_2,a_3$ and replaces $a_4, a_6$ by $a_4 - 5\sum_{P \in S}\mathrm{veluT}(P)$, $a_6 - b_2\sum_{P\in S}\mathrm{veluT}(P) - 7\sum_{P\in S}\mathrm{veluW}(P)$. Let $(x_1,y_1)$, $(x_2,y_2)$ be nonsingular affine points of $W$ annihilated by $3$ with $x_1 \neq x_2$. Let $\Omega$ be an algebraically closed field of characteristic zero which is an algebraic extension of the fraction field of the Witt vectors $\mathbb{W}(p,k)$. Then there exist: a valuation subring $B \subseteq \Omega$ and a ring isomorphism $\varphi : k \cong B/\mathfrak{m}_B$; an elliptic Weierstrass curve $E'$ over $B$ whose reduction has nonzero discriminant and satisfies $1 \cdot (E' \bmod \mathfrak{m}_B) = \varphi_* W$ (the hypothesis `hv'`); a point $Q'$ of $E'$ over $\Omega$ of exact order $2n+1$ whose reduction corresponds to $\varphi_* Q_0$ under the bijection on points attached to `hv'`; a variable change $\gamma$ over $\Omega$ with $\gamma \cdot E'_\Omega$ equal to the Vélu quotient of $E'_\Omega$ by `oddOrderSummingSet Q' n`; a further Weierstrass curve $E_1'$ over $B$ with nonzero reduced discriminant such that $E_1'$ base changed to $\Omega$ is that Vélu quotient and $E_1' \bmod \mathfrak{m}_B$ is $\varphi_*(W/S_0)$; elements $e_1,t_1,e_2,t_2 \in B$ giving nonsingular affine points of $E'_\Omega$ and $e_1',t_1',e_2',t_2' \in B$ giving nonsingular affine points of the Vélu quotient of $E'_\Omega$; such that $(e_i,t_i)$ are annihilated by $3$, the reductions of $(e_1,t_1)$ and $(e_2,t_2)$ correspond to $\varphi_*(x_1,y_1)$ and $\varphi_*(x_2,y_2)$, the bijection attached to $\gamma$ carries $(e_i',t_i')$ to $(e_i,t_i)$, and the residues of $e_1',t_1',e_2',t_2'$ in $B/\mathfrak{m}_B$ are $\varphi$ of $u_0^{-2}(x_i-r_0)$ and $u_0^{-3}(y_i-t_0-s_0(x_i-r_0))$ respectively, where $\gamma_0 = (u_0,r_0,s_0,t_0)$.
--
--   This is Deuring's lifting theorem in a rigidified form adapted to residue characteristic $2$: the elliptic curve, its cyclic subgroup of odd order $2n+1$, the isomorphism onto the Vélu quotient and the marked points of order three are all lifted simultaneously from $k$ to a valuation subring of an algebraically closed algebraic extension of $\mathrm{Frac}\,\mathbb{W}(k)$, with level-three marking replacing the Legendre (level-two) marking available when $2 \neq 0$. It is used in the companion statement on lifting a curve together with a variable change realising the Vélu quotient and the reduction of three-torsion when $2 = 0$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_valuationSubring_lift_variableChange_veluQuotient_apply_threeTorsion_eq_of_smul_eq_veluQuotient.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_ReduceHom
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Definitions.Def_WeierstrassCurve_RatPointHom
import Definitions.Def_WeierstrassCurve_Velu
import Definitions.Def_WeierstrassCurve_OddOrderSummingSet

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped Classical in

theorem WeierstrassCurve.exists_valuationSubring_lift_variableChange_veluQuotient_apply_threeTorsion_eq_of_smul_eq_veluQuotient
    (p : ℕ) [Fact p.Prime] {k : Type} [Field k] [IsAlgClosed k] [CharP k p] [DecidableEq k]
    (h3 : (3 : k) ≠ 0)
    (W : WeierstrassCurve k) [W.IsElliptic] (n : ℕ) (hm : ((2 * n + 1 : ℕ) : k) ≠ 0)
    (hsq : ¬ IsSquare (2 * n + 1)) (Q₀ : W.toAffine.Point) (hQ₀ : addOrderOf Q₀ = 2 * n + 1)
    (γ₀ : WeierstrassCurve.VariableChange k)
    (hγ₀ : γ₀ • W = W.veluQuotient (W.oddOrderSummingSet Q₀ n))
    {x₁ y₁ x₂ y₂ : k} (h₁ : W.toAffine.Nonsingular x₁ y₁) (h₂ : W.toAffine.Nonsingular x₂ y₂)
    (hP₁ : (3 : ℤ) • (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁) = 0)
    (hP₂ : (3 : ℤ) • (WeierstrassCurve.Affine.Point.some x₂ y₂ h₂) = 0)
    (hx : x₁ ≠ x₂)
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [CharZero Ω]
    [Algebra (FractionRing (WittVector p k)) Ω]
    [Algebra.IsAlgebraic (FractionRing (WittVector p k)) Ω] :
    ∃ (B : ValuationSubring Ω) (φ : k ≃+* IsLocalRing.ResidueField B)
      (E' : WeierstrassCurve B)
      (_ : E'.IsElliptic) (hΔ' : (E'.map (IsLocalRing.residue B)).Δ ≠ 0)
      (hv' : (1 : WeierstrassCurve.VariableChange (IsLocalRing.ResidueField B)) •
        E'.map (IsLocalRing.residue B) = W.map φ.toRingHom)
      (Q' : (E'.map B.subtype).toAffine.Point) (_ : addOrderOf Q' = 2 * n + 1)
      (_ : WeierstrassCurve.ratPointHom φ.toRingHom Q₀ =
        (WeierstrassCurve.Affine.Point.equivOfVariableChangeEq hv').symm
          (WeierstrassCurve.reduceHom hΔ' Q'))
      (γ : WeierstrassCurve.VariableChange Ω)
      (hγ : γ • E'.map B.subtype =
        (E'.map B.subtype).veluQuotient ((E'.map B.subtype).oddOrderSummingSet Q' n))
      (E₁' : WeierstrassCurve B) (_ : (E₁'.map (IsLocalRing.residue B)).Δ ≠ 0)
      (_ : (1 : WeierstrassCurve.VariableChange Ω) • E₁'.map B.subtype =
        (E'.map B.subtype).veluQuotient ((E'.map B.subtype).oddOrderSummingSet Q' n))
      (_ : (1 : WeierstrassCurve.VariableChange (IsLocalRing.ResidueField B)) •
          E₁'.map (IsLocalRing.residue B) =
        (W.veluQuotient (W.oddOrderSummingSet Q₀ n)).map φ.toRingHom)
      (e₁ t₁ e₂ t₂ : B)
      (hT₁ : (E'.map B.subtype).toAffine.Nonsingular e₁ t₁)
      (hT₂ : (E'.map B.subtype).toAffine.Nonsingular e₂ t₂)
      (e'₁ t'₁ e'₂ t'₂ : B)
      (hT'₁ : ((E'.map B.subtype).veluQuotient
        ((E'.map B.subtype).oddOrderSummingSet Q' n)).toAffine.Nonsingular e'₁ t'₁)
      (hT'₂ : ((E'.map B.subtype).veluQuotient
        ((E'.map B.subtype).oddOrderSummingSet Q' n)).toAffine.Nonsingular e'₂ t'₂),
      (3 : ℤ) • WeierstrassCurve.Affine.Point.some _ _ hT₁ = 0 ∧
      (3 : ℤ) • WeierstrassCurve.Affine.Point.some _ _ hT₂ = 0 ∧
      WeierstrassCurve.ratPointHom φ.toRingHom (.some x₁ y₁ h₁) =
        (WeierstrassCurve.Affine.Point.equivOfVariableChangeEq hv').symm
          (WeierstrassCurve.reduceHom hΔ' (.some _ _ hT₁)) ∧
      WeierstrassCurve.ratPointHom φ.toRingHom (.some x₂ y₂ h₂) =
        (WeierstrassCurve.Affine.Point.equivOfVariableChangeEq hv').symm
          (WeierstrassCurve.reduceHom hΔ' (.some _ _ hT₂)) ∧
      WeierstrassCurve.Affine.Point.equivOfVariableChangeEq hγ (.some _ _ hT'₁) = .some _ _ hT₁ ∧
      WeierstrassCurve.Affine.Point.equivOfVariableChangeEq hγ (.some _ _ hT'₂) = .some _ _ hT₂ ∧
      IsLocalRing.residue B e'₁ = φ (WeierstrassCurve.Affine.vcXInv γ₀ x₁) ∧
      IsLocalRing.residue B t'₁ = φ (WeierstrassCurve.Affine.vcYInv γ₀ x₁ y₁) ∧
      IsLocalRing.residue B e'₂ = φ (WeierstrassCurve.Affine.vcXInv γ₀ x₂) ∧
      IsLocalRing.residue B t'₂ = φ (WeierstrassCurve.Affine.vcYInv γ₀ x₂ y₂) := by sorry
