-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_reduceHom_eq_of_nsmul_eq_zero_of_natCast_ne_zero
-- name    : WeierstrassCurve.exists_reduceHom_eq_of_nsmul_eq_zero_of_natCast_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.985064+00:00
-- url     : https://prove2.me/theorems/0e002459-c676-51e7-a909-d2a009b3d663
-- title:
--   Lifting ℓ-torsion along good reduction over a valuation subring
-- statement:
--   Let $L$ be an algebraically closed field of characteristic $0$ and let $A \subseteq L$ be a valuation subring, with residue field $\kappa =$ `ResidueField A` and residue map $\mathrm{residue}\,A : A \to \kappa$. Let $W$ be a Weierstrass curve over $A$ and assume that the reduced curve $W \otimes \kappa$, obtained by applying $\mathrm{residue}\,A$ to the coefficients of $W$, has nonzero discriminant, $\Delta(W \otimes \kappa) \neq 0$. Let $\ell$ be a natural number whose image in $\kappa$ is nonzero, and let $Q_0$ be a point of the affine curve attached to $W \otimes \kappa$ with $\ell \cdot Q_0 = 0$. Then there is a point $Q$ of the affine curve attached to the base change of $W$ along the inclusion $A \hookrightarrow L$, i.e. a point of $W(L)$, such that $\ell \cdot Q = 0$ and $Q$ reduces to $Q_0$ under the additive map `reduceHom`. Here `reduceHom` sends the point at infinity to the point at infinity, sends an affine point $(x,y)$ with $x \in A$ (whence also $y \in A$) to the point with coordinates the residues of $x$ and $y$, and sends an affine point with $x \notin A$ to the point at infinity. No primality assumption on $\ell$ is made.
--
--   This is the surjectivity half of the classical statement that, for a Weierstrass model with good reduction, reduction is an isomorphism on torsion of order prime to the residue characteristic (Silverman, Prop. VII.3.1(b)); the residue characteristic is unrestricted here, only $\ell$ being invertible in $\kappa$ is required. It is used in the construction of the modular polynomial data, where fibre polynomials are compared with products over $j$-invariants of quotient curves, and in the variable-change argument at residue characteristic $2$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_reduceHom_eq_of_nsmul_eq_zero_of_natCast_ne_zero.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_ReduceHom

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open WeierstrassCurve IsLocalRing

theorem WeierstrassCurve.exists_reduceHom_eq_of_nsmul_eq_zero_of_natCast_ne_zero
    {L : Type*} [Field L] [DecidableEq L] [IsAlgClosed L] [CharZero L]
    (A : ValuationSubring L) [DecidableEq (ResidueField A)]
    (W : WeierstrassCurve A) (hΔ : (W.map (residue A)).Δ ≠ 0)
    {ℓ : ℕ} (hℓ : (ℓ : ResidueField A) ≠ 0)
    (Q₀ : (W.map (residue A)).toAffine.Point) (hQ₀ : ℓ • Q₀ = 0) :
    ∃ Q : (W.map A.subtype).toAffine.Point, ℓ • Q = 0 ∧ reduceHom hΔ Q = Q₀ := by sorry
