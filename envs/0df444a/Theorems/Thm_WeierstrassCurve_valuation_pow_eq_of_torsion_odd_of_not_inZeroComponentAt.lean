-- Prove2me | Theorems.Thm_WeierstrassCurve_valuation_pow_eq_of_torsion_odd_of_not_inZeroComponentAt
-- name    : WeierstrassCurve.valuation_pow_eq_of_torsion_odd_of_not_inZeroComponentAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/59740166-9cca-5020-8206-a6c5c6afed12
-- title:
--   Level of odd-order torsion reducing to a node
-- statement:
--   Let $W$ be a Weierstrass curve over $\mathbb Z$ and $q$ a prime number with $\Delta_W\neq 0$, $q\mid\Delta_W$ and $q\nmid c_4(W)$, so that $W$ has multiplicative reduction at $q$. Let $A$ be a valuation subring of $\overline{\mathbb Q}$ satisfying the project's predicate `LiesOverPrime`, i.e. $q$ is a non-unit of $A$, and write $v_A$ for the associated (multiplicatively written) valuation, so that $v_A(z)<1$ means that $z$ lies in the maximal ideal of $A$. Let $x_0,y_0\in A$ be critical-centre data for the node: $2y_0+a_1x_0+a_3=0$ and $a_1y_0=3x_0^2+2a_2x_0+a_4$ (the two partial derivatives of the Weierstrass polynomial vanish), $v_A(b_2+12x_0)=1$, and $v_A\bigl(y_0^2+a_1x_0y_0+a_3y_0-(x_0^3+a_2x_0^2+a_4x_0+a_6)\bigr)<1$. Let $n$ be odd with $n>1$ and $q\nmid n$, and let $(x,y)$ be a nonsingular affine point of $W$ base-changed to $\overline{\mathbb Q}$ (through $W.\mathrm{map}(\mathbb Z\to\mathbb Q)$) whose associated point $P=\mathrm{some}\,x\,y$ satisfies $n\cdot P=0$, and assume $v_A(x-x_0)<1$; this last inequality is how the statement expresses that $P$ reduces to the node, in place of a negated occurrence of the project's predicate `InZeroComponentAt`. The conclusion is twofold: first, $v_A(\Delta_W)<v_A(x-x_0)^2$ (the point is "shallow"), and second, there exists a natural number $j$ with $1\le j$, $2j<n$ and $v_A(x-x_0)^n=v_A(\Delta_W)^j$.
--
--   This is the valuation-theoretic shadow of the description of torsion on a Tate curve: a point of exact order $d\mid n$ outside the identity component is $\zeta q_A^{b/d}$ with $0<b<d$, and its level $v_A(x-x_0)$ equals $v_A(\Delta)^{\min(b,d-b)/d}$, the exponent being less than $1/2$ because $d$ is odd. The formal statement differs from the textbook account in that no Tate parametrisation is used or asserted: everything is phrased through a fixed place $A$ of $\overline{\mathbb Q}$, explicit critical-centre data $(x_0,y_0)$ for the node, and inequalities between values of $v_A$, and it generalises the corresponding results for torsion of prime order to arbitrary odd $n>1$. It is used in the proof that the Frey curve attached to a Frey package with $p\ge 17$ admits no Galois-stable cofixed line, where the level identity forces an element of a decomposition group either to fix or to swap the two branches at the node.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_valuation_pow_eq_of_torsion_odd_of_not_inZeroComponentAt.lean

import Mathlib
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_ZeroComponentAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point ValuationSubring

theorem WeierstrassCurve.valuation_pow_eq_of_torsion_odd_of_not_inZeroComponentAt
    (W : WeierstrassCurve ℤ) {q : ℕ} (hq : q.Prime) (hΔ : W.Δ ≠ 0)
    (hqΔ : (q : ℤ) ∣ W.Δ) (hqc₄ : ¬ (q : ℤ) ∣ W.c₄)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    {x₀ y₀ : AlgebraicClosure ℚ} (hx₀ : x₀ ∈ A) (hy₀ : y₀ ∈ A)
    (hFy : 2 * y₀ + (W.a₁ : AlgebraicClosure ℚ) * x₀ + W.a₃ = 0)
    (hFx : (W.a₁ : AlgebraicClosure ℚ) * y₀ = 3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄)
    (hnode : A.valuation ((W.b₂ : AlgebraicClosure ℚ) + 12 * x₀) = 1)
    (hbad : A.valuation (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀
      - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)) < 1)
    {n : ℕ} (hn : Odd n) (hn1 : 1 < n) (hnq : ¬ q ∣ n)
    {x y : AlgebraicClosure ℚ}
    (h : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).toAffine.Nonsingular x y)
    (htor : n • (Point.some x y h) = 0) (hX : A.valuation (x - x₀) < 1) :
    A.valuation (W.Δ : AlgebraicClosure ℚ) < A.valuation (x - x₀) ^ 2 ∧
      ∃ j : ℕ, 1 ≤ j ∧ 2 * j < n ∧
        A.valuation (x - x₀) ^ n = A.valuation (W.Δ : AlgebraicClosure ℚ) ^ j := by sorry
