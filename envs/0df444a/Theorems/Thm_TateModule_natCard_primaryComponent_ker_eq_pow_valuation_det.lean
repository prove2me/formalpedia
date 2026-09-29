-- Prove2me | Theorems.Thm_TateModule_natCard_primaryComponent_ker_eq_pow_valuation_det
-- name    : TateModule.natCard_primaryComponent_ker_eq_pow_valuation_det
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/fb778cc9-0135-5c6a-81d0-862ad03416e9
-- title:
--   Order of the p-primary kernel via the Tate determinant
-- statement:
--   Fix a prime $p$ and an additive abelian group $M$, and let $r$ be a natural number. Assume that for every $n$ the $\mathbb{Z}$-torsion submodule $M[p^n]$, i.e. `Submodule.torsionBy ℤ M ((p ^ n : ℕ) : ℤ)`, is finite of cardinality $(p^n)^r$. Let $\alpha : M \to M$ be an additive endomorphism. Here [`TateModule p M`](def/EllipticCurve_TateModule.html#L15) is the additive subgroup of sequences $x : \mathbb{N} \to M$ satisfying $p^n \cdot x_n = 0$ and $p \cdot x_{n+1} = x_n$ for all $n$, carrying its natural $\mathbb{Z}_p$-module structure, and [`TateModule.rep p M (Module.End ℤ M)`](def/EllipticCurve_TateModule.html#L174) is the monoid homomorphism sending an endomorphism of $M$ to the $\mathbb{Z}_p$-linear endomorphism of [`TateModule p M`](def/EllipticCurve_TateModule.html#L15) acting coordinatewise; write $T_p\alpha$ for the image of $\alpha$, viewed as a $\mathbb{Z}$-linear map. Assume $\det(T_p\alpha) \neq 0$ in $\mathbb{Z}_p$. Then the $p$-primary component of $\ker \alpha$, that is `AddCommGroup.primaryComponent α.ker p`, has cardinality $p^{v_p(\det(T_p\alpha))}$, where $v_p$ denotes the $p$-adic valuation of a nonzero $p$-adic integer. In particular the asserted equality of `Nat.card` values records that this $p$-primary component is finite of that order.
--
--   This is the classical computation, in the style of Tate's determinant formula for endomorphisms of abelian varieties, of the number of $p$-power-torsion points killed by an endomorphism in terms of the determinant of its action on the $p$-adic Tate module; neither surjectivity of $\alpha$ nor a priori finiteness of $\ker\alpha$ is assumed. It feeds the identification of the characteristic polynomial of the action of an endomorphism on a Tate module in [`TateModule.charpoly_toMatrix_rep_eq_map_of_natCard_primaryComponent_ker_aeval`](thm.html#TateModule.charpoly_toMatrix_rep_eq_map_of_natCard_primaryComponent_ker_aeval), and the vanishing criterion [`ModularCurve.exists_pow_smul_eq_zero_of_forall_tateModule_eq_zero`](thm.html#ModularCurve.exists_pow_smul_eq_zero_of_forall_tateModule_eq_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_TateModule_natCard_primaryComponent_ker_eq_pow_valuation_det.lean

import Mathlib.GroupTheory.Torsion
import Mathlib.LinearAlgebra.Determinant
import Definitions.Def_EllipticCurve_TateModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem TateModule.natCard_primaryComponent_ker_eq_pow_valuation_det (p : ℕ) [Fact p.Prime] {M : Type}
    [AddCommGroup M] (r : ℕ) (hcard : ∀ n : ℕ, Nat.card (Submodule.torsionBy ℤ M ((p ^ n : ℕ) : ℤ)) = (p ^ n) ^ r)
    (α : M →+ M) (hdet : LinearMap.det (TateModule.rep p M (Module.End ℤ M) α.toIntLinearMap) ≠ 0) :
    Nat.card (AddCommGroup.primaryComponent α.ker p) =
      p ^ (LinearMap.det (TateModule.rep p M (Module.End ℤ M) α.toIntLinearMap)).valuation := by sorry
