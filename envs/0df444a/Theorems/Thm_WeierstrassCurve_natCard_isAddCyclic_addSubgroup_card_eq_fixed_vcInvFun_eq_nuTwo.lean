-- Prove2me | Theorems.Thm_WeierstrassCurve_natCard_isAddCyclic_addSubgroup_card_eq_fixed_vcInvFun_eq_nuTwo
-- name    : WeierstrassCurve.natCard_isAddCyclic_addSubgroup_card_eq_fixed_vcInvFun_eq_nuTwo
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/29c5b42e-ed21-58ba-b7b8-54ea07fd9c77
-- title:
--   Cyclic N-subgroups of y²=x³+Ax stable under [i]
-- statement:
--   Let $L$ be an algebraically closed field equipped with a $\mathbb{Q}$-algebra structure (hence of characteristic zero) and with decidable equality, let $A \in L$ be nonzero, let $u$ be a unit of $L$ with $u^2 = -1$, and let $N$ be a nonzero natural number. Consider the Weierstrass curve $W = \langle 0,0,0,A,0\rangle$ over $L$, that is $y^2 = x^3 + Ax$, and the group $W.\mathrm{toAffine}.\mathrm{Point}$ of its affine points together with the point at infinity. For the variable change $\gamma = \langle u,0,0,0\rangle$, the map `Point.vcInvFun` sends the point at infinity of $W$ to that of $\gamma \bullet W$ and an affine point $(x,y)$ to the point with coordinates $((u^{-1})^2 x, (u^{-1})^3 y)$ on $\gamma \bullet W$; since $(u^{-1})^2 = -1$ this is $(x,y) \mapsto (-x, (u^{-1})^3 y)$. The assertion is that the number of subgroups $H$ of $W.\mathrm{toAffine}.\mathrm{Point}$ which are cyclic, satisfy $\#H = N$, and are stable in the sense that for every $T \in H$ there is $T' \in H$ with `Point.vcInvFun` $\gamma\, W\, T$ heterogeneously equal to $T'$ (the two points lying in the types of points of $\gamma \bullet W$ and of $W$ respectively), equals $\nu_2(N) = \#\{x \in \mathbb{Z}/N : x^2 + 1 = 0\}$.
--
--   This is the count of cyclic subgroups of order $N$ on a curve with $j = 1728$ that are stable under the automorphism $[i]$, i.e. the contribution of the elliptic points of order two to the standard count of moduli points on $Y_0(N)$. It supplies the term $\nu_2(N)$ in [`ModularCurve.two_mul_natCard_moduliPoint_j_eq_1728_eq_dedekindPsi_add_nuTwo`](thm.html#ModularCurve.two_mul_natCard_moduliPoint_j_eq_1728_eq_dedekindPsi_add_nuTwo).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_natCard_isAddCyclic_addSubgroup_card_eq_fixed_vcInvFun_eq_nuTwo.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Definitions.Def_ModularCurve_GenusNumerics

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine ModularCurve

theorem WeierstrassCurve.natCard_isAddCyclic_addSubgroup_card_eq_fixed_vcInvFun_eq_nuTwo
    {L : Type*} [Field L] [DecidableEq L] [Algebra ℚ L] [IsAlgClosed L]
    (A : L) (hA : A ≠ 0) (u : Lˣ) (hu : (u : L) ^ 2 = -1) (N : ℕ) (hN : N ≠ 0) :
    Nat.card {H : AddSubgroup (⟨0, 0, 0, A, 0⟩ : WeierstrassCurve L).toAffine.Point //
        IsAddCyclic H ∧ Nat.card H = N ∧
        ∀ T ∈ H, ∃ T' ∈ H, HEq (Point.vcInvFun (⟨u, 0, 0, 0⟩ : VariableChange L)
          (⟨0, 0, 0, A, 0⟩ : WeierstrassCurve L).toAffine T) T'}
      = nuTwo N := by sorry
