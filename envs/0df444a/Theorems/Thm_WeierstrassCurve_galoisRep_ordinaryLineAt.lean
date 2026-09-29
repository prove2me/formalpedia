-- Prove2me | Theorems.Thm_WeierstrassCurve_galoisRep_ordinaryLineAt
-- name    : WeierstrassCurve.galoisRep_ordinaryLineAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.985064+00:00
-- url     : https://prove2.me/theorems/adfd3588-94ae-5d94-8e6b-9b67f34e1c8a
-- title:
--   Inertia acts trivially modulo a proper subspace of E[p]
-- statement:
--   Let $W$ be a Weierstrass curve over $\mathbb{Z}$ and $p$ an odd prime. Assume $W.\Delta \neq 0$; that $W$ is a semistable model, i.e. for every prime $q$ with $q \mid W.\Delta$ one has $q \nmid W.c_4$; and the ordinarity-or-multiplicativity alternative that either $p \mid W.\Delta$, or there is an index $i$ with $1 \le i < (p^2-1)/2$ such that the $i$-th coefficient of the division polynomial `W.pre\Psi' p` is not divisible by $p$. Let $A$ be a valuation subring of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` lying over $p$, in the sense that the image of $p$ in $\overline{\mathbb{Q}}$ is a nonunit of $A$. Then there is a $\mathbb{Z}/p$-submodule $L$ of the $p$-torsion $\{P : pP = 0\}$ of the group of points of $W$ base changed to $\overline{\mathbb{Q}}$ such that $L \neq \top$ and, for every $\sigma$ in the image in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of the inertia subgroup of $A$ inside its decomposition subgroup, and every $p$-torsion point $v$, one has $\sigma v - v \in L$, the action being the $\mathbb{Z}/p$-linear Galois action `galoisRepModuleEnd`. Only properness of $L$ is asserted, not that it is a line.
--
--   This is the assertion that inertia at $p$ acts trivially on the quotient of $E[p]$ by a proper subspace, for a semistable integral model which at $p$ has either multiplicative reduction or good reduction with a coefficient condition on the $p$-division polynomial expressing ordinarity. It supplies the ordinary branch of the local hypothesis at $p$ used by [`WeierstrassCurve.residualGaloisRepOf_restrict_index_two`](thm.html#WeierstrassCurve.residualGaloisRepOf_restrict_index_two) and by [`WeierstrassCurve.ofResidualGaloisRep_residualGaloisRepOf_isOrdinaryAt`](thm.html#WeierstrassCurve.ofResidualGaloisRep_residualGaloisRepOf_isOrdinaryAt).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_galoisRep_ordinaryLineAt.lean

import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Definitions.Def_GaloisRep_Residual

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem WeierstrassCurve.galoisRep_ordinaryLineAt (W : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hΔ : W.Δ ≠ 0)
    (hW : W.IsSemistableModel)
    (hord : (p : ℤ) ∣ W.Δ ∨ ∃ i, 1 ≤ i ∧ i < (p ^ 2 - 1) / 2 ∧ ¬ (p : ℤ) ∣ (W.preΨ' p).coeff i)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p) :
    ∃ L : Submodule (ZMod p)
        (Submodule.torsionBy ℤ ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point p),
      L ≠ ⊤ ∧ ∀ σ ∈ A.inertiaSubgroupIn ℚ,
        ∀ v : Submodule.torsionBy ℤ ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point p,
          WeierstrassCurve.Affine.Point.galoisRepModuleEnd (K := AlgebraicClosure ℚ) ℚ
            (W.map (Int.castRingHom ℚ)) p σ v - v ∈ L := by sorry
