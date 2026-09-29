-- Prove2me | Theorems.Thm_TateCurve_exists_primitiveRoot_equiv_torsion_algebraicClosure_padic_of_five_le
-- name    : TateCurve.exists_primitiveRoot_equiv_torsion_algebraicClosure_padic_of_five_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.134728+00:00
-- url     : https://prove2.me/theorems/48e0133a-a86e-5151-b068-6b4054dfcb42
-- title:
--   Galois-equivariant parametrisation of Tate-curve p-torsion over ℚ̄ₚ
-- statement:
--   Let $p$ be a prime with $5 \le p$, and let $q_T \in \mathbb{Q}_p$ be nonzero with $\|q_T\|_{\ge 0} < 1$ (nonnegative-real norm strictly below $1$). Write $E$ for the Weierstrass curve $\langle a_1,a_2,a_3,a_4,a_6\rangle = \langle 1,0,0,a_4(q_T),a_6(q_T)\rangle$ attached to $q_T$ by [`TateCurve.curve`](def/TateCurve_QSeries.html#L185), and consider its base change to $\overline{\mathbb{Q}}_p =$ `AlgebraicClosure ℚ_[p]` and the group of affine points thereof. The assertion is that there exist $\zeta, t \in \overline{\mathbb{Q}}_p$ with $\zeta$ a primitive $p$-th root of unity and $t^p$ equal to the image of $q_T$ under the structure map $\mathbb{Q}_p \to \overline{\mathbb{Q}}_p$, together with a bijection $\varphi$ from $\mathbb{Z}/p \times \mathbb{Z}/p$ onto the $\mathbb{Z}$-torsion submodule $\{P : (p:\mathbb{Z})\cdot P = 0\}$ of $E(\overline{\mathbb{Q}}_p)$, such that: (i) $\varphi$ is additive on underlying points, i.e. $\varphi(a+b) = \varphi(a) + \varphi(b)$ in $E(\overline{\mathbb{Q}}_p)$ for all $a, b$; and (ii) for every $\mathbb{Q}_p$-algebra automorphism $\sigma$ of $\overline{\mathbb{Q}}_p$ and all natural numbers $e, c$ with $\sigma\zeta = \zeta^e$ and $\sigma t = \zeta^c t$, one has $\sigma \cdot \varphi(i,j) = \varphi(e\cdot i + c\cdot j,\, j)$ for all $i, j \in \mathbb{Z}/p$, the action being the one induced by $\sigma$ on points.
--
--   This is the Tate parametrisation of the $p$-torsion of a Tate curve over a $p$-adic field, packaged as an additive bijection $(\mathbb{Z}/p)^2 \to E_q[p](\overline{\mathbb{Q}}_p)$ whose Galois action is upper triangular with diagonal entries the cyclotomic character and the trivial character; no divisibility condition on the valuation of $q_T$ is imposed. It feeds the construction of finite flat prolongations of the $p$-torsion over $\mathbb{Z}_p$ and the local–global comparison of torsion modules used in the analysis of Frey curves at primes of multiplicative reduction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_TateCurve_exists_primitiveRoot_equiv_torsion_algebraicClosure_padic_of_five_le.lean

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

theorem TateCurve.exists_primitiveRoot_equiv_torsion_algebraicClosure_padic_of_five_le
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (qT : ℚ_[p]) (hqT0 : qT ≠ 0) (hqT1 : ‖qT‖₊ < 1) :
    letI : DecidableEq (AlgebraicClosure ℚ_[p]) := Classical.decEq _
    ∃ (ζ t : AlgebraicClosure ℚ_[p]), IsPrimitiveRoot ζ p ∧
      t ^ p = algebraMap ℚ_[p] (AlgebraicClosure ℚ_[p]) qT ∧
    ∃ φ : (ZMod p × ZMod p) ≃
          Submodule.torsionBy ℤ ((TateCurve.curve qT)⁄(AlgebraicClosure ℚ_[p])).Point p,
      (∀ a b, (φ (a + b) : ((TateCurve.curve qT)⁄(AlgebraicClosure ℚ_[p])).Point)
              = (φ a : ((TateCurve.curve qT)⁄(AlgebraicClosure ℚ_[p])).Point)
              + (φ b : ((TateCurve.curve qT)⁄(AlgebraicClosure ℚ_[p])).Point)) ∧
      ∀ (σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]) (e c : ℕ),
        σ ζ = ζ ^ e → σ t = ζ ^ c * t →
        ∀ i j : ZMod p, σ • (φ (i, j)) = φ (e • i + c • j, j) := by sorry
