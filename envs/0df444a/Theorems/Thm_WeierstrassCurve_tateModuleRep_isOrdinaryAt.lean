-- Prove2me | Theorems.Thm_WeierstrassCurve_tateModuleRep_isOrdinaryAt
-- name    : WeierstrassCurve.tateModuleRep_isOrdinaryAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/9eb7c6fe-ae4c-5cc1-9192-4fa997a2fde2
-- title:
--   Ordinarity of the Tate module at multiplicative and good ordinary p
-- statement:
--   Let $W$ be a Weierstrass curve over $\mathbb{Z}$, let $p$ be a prime, and assume: the discriminant satisfies $W.\Delta \neq 0$; $W$ is a semistable model, i.e. `W.IsSemistableModel` holds, meaning that for every prime $q$ dividing $W.\Delta$ one has $q \nmid W.c_4$; the counting hypothesis `hcard` that for every $n$ the subgroup of elements killed by $p^n$ in the group of points of $W$ base changed along $\mathbb{Z} \to \mathbb{Q}$ and then to $\mathrm{AlgebraicClosure}\ \mathbb{Q}$ has exactly $(p^n)^2$ elements; and the disjunction `hord` that either $p$ is not a good prime for $W$ (the negation of $p \nmid W.\Delta$) or $p \nmid W.\mathrm{apOfModel}\ p$, where $\mathrm{apOfModel}$ is $\#\mathbb{Z}/p + 1$ minus the number of points of the reduction $W \bmod p$ over $\mathbb{Z}/p$. The conclusion is that the rank-two continuous representation `tateModuleRep` of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q}) = \mathrm{AlgebraicClosure}\ \mathbb{Q} \simeq_{\mathbb{Q}} \mathrm{AlgebraicClosure}\ \mathbb{Q}$ on the Tate module of $W_{\mathbb{Q}}$ — the group of sequences $(x_n)$ of $\overline{\mathbb{Q}}$-points with $p^n x_n = 0$ and $p\,x_{n+1} = x_n$, given the $\mathbb{Z}_p$-basis attached to `hcard` — is ordinary at $p$: for every valuation subring $P$ of $\mathrm{AlgebraicClosure}\ \mathbb{Q}$ with $p$ a non-unit of $P$, there is a $\mathbb{Z}_p$-submodule $L$ of the Tate module which is the span of $b\,0$ for some basis $b$ indexed by $\mathrm{Fin}\ 2$, such that $L$ is stable under every element of the decomposition subgroup of $P$ over $\mathbb{Q}$, and $\rho(\sigma)v - v \in L$ for every $\sigma$ in the inertia subgroup of $P$ (viewed inside the decomposition subgroup) and every $v$ in the Tate module.
--
--   This is the local ordinarity condition at $p$ for the $p$-adic Tate module of a semistable integral Weierstrass model, covering both the multiplicative case ($p \mid \Delta$) and the good ordinary case ($p \nmid \Delta$, $p \nmid a_p$), with no restriction on $p$. It feeds the statements [`WeierstrassCurve.tateModuleRep_baseChangeAlong_condition_and_charpoly_flat_odd`](thm.html#WeierstrassCurve.tateModuleRep_baseChangeAlong_condition_and_charpoly_flat_odd) and [`WeierstrassCurve.tateModuleRep_baseChangeAlong_condition_and_charpoly_flat_odd_finiteAt`](thm.html#WeierstrassCurve.tateModuleRep_baseChangeAlong_condition_and_charpoly_flat_odd_finiteAt), where the ordinary local condition at $p$ is one of the deformation-theoretic hypotheses on the representation attached to the Frey curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_tateModuleRep_isOrdinaryAt.lean

import Definitions.Def_GaloisRep_LocalConditions
import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_FLTPrelim_Modularity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem WeierstrassCurve.tateModuleRep_isOrdinaryAt (W : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime]
    (hΔ : W.Δ ≠ 0) (hW : W.IsSemistableModel)
    (hcard : ∀ n : ℕ, Nat.card (Submodule.torsionBy ℤ
      ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point ((p ^ n : ℕ) : ℤ)) = (p ^ n) ^ 2)
    (hord : ¬ W.IsGoodPrimeFor p ∨ ¬ (p : ℤ) ∣ W.apOfModel p) :
    ((W.map (Int.castRingHom ℚ)).tateModuleRep p hcard).IsOrdinaryAt p := by sorry
