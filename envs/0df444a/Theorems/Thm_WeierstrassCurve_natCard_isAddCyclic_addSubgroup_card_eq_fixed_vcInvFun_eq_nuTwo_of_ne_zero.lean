-- Prove2me | Theorems.Thm_WeierstrassCurve_natCard_isAddCyclic_addSubgroup_card_eq_fixed_vcInvFun_eq_nuTwo_of_ne_zero
-- name    : WeierstrassCurve.natCard_isAddCyclic_addSubgroup_card_eq_fixed_vcInvFun_eq_nuTwo_of_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/6797a880-135d-5b26-ba72-743789a30b3a
-- title:
--   Cyclic N-subgroups of y²=x³+Ax stable under [i]
-- statement:
--   Let $L$ be an algebraically closed field with decidable equality, let $A \in L$ with $A \neq 0$, let $u \in L^{\times}$ satisfy $u^{2} = -1$, assume $2 \neq 0$ in $L$, and let $N$ be a natural number whose image in $L$ is nonzero (so in particular $N \geq 1$). Consider the Weierstrass curve $W = \langle 0,0,0,A,0\rangle$, i.e. $y^{2} = x^{3} + Ax$, and the group $W^{\mathrm{aff}}(L)$ of affine points. The variable change $C = (u,0,0,0)$ transports points by `Point.vcInvFun`, which sends the point at infinity to itself and a point $(x,y)$ to the point $((u^{-1})^{2}(x-0),\,(u^{-1})^{3}(y-0-0\cdot(x-0))) = (-x, uy)$ on $C \bullet W$; since $u^{2}=-1$, the curve $C \bullet W$ equals $W$, so this is the automorphism $[i]$ of $W^{\mathrm{aff}}(L)$, presented across that equality of curves. The assertion is that the number of additive subgroups $H \leq W^{\mathrm{aff}}(L)$ which are cyclic, have exactly $N$ elements, and satisfy: every $T \in H$ admits some $T' \in H$ with `vcInvFun C W.toAffine T` heterogeneously equal to $T'$ (i.e. $[i]$ maps $H$ into $H$), equals `nuTwo N`, the number of $x \in \mathbb{Z}/N\mathbb{Z}$ with $x^{2} + 1 = 0$.
--
--   This enumerates the cyclic subgroups of order $N$ on a curve with $j$-invariant $1728$ that are stable under the extra automorphism $[i]$, in any characteristic prime to $2N$; it is the fixed-point contribution in the Burnside-type count of the fibre of $Y_0(N)$ above $j = 1728$. It feeds the count of moduli points over $j = 1728$ and, through that, the enumeration of elliptic and supersingular points used in the genus and census computations for modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_natCard_isAddCyclic_addSubgroup_card_eq_fixed_vcInvFun_eq_nuTwo_of_ne_zero.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Definitions.Def_ModularCurve_GenusNumerics

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine ModularCurve

theorem WeierstrassCurve.natCard_isAddCyclic_addSubgroup_card_eq_fixed_vcInvFun_eq_nuTwo_of_ne_zero
    {L : Type*} [Field L] [DecidableEq L] [IsAlgClosed L]
    (A : L) (hA : A ≠ 0) (u : Lˣ) (hu : (u : L) ^ 2 = -1)
    (h2 : (2 : L) ≠ 0) (N : ℕ) (hN : (N : L) ≠ 0) :
    Nat.card {H : AddSubgroup (⟨0, 0, 0, A, 0⟩ : WeierstrassCurve L).toAffine.Point //
        IsAddCyclic H ∧ Nat.card H = N ∧
        ∀ T ∈ H, ∃ T' ∈ H, HEq (Point.vcInvFun (⟨u, 0, 0, 0⟩ : VariableChange L)
          (⟨0, 0, 0, A, 0⟩ : WeierstrassCurve L).toAffine T) T'}
      = nuTwo N := by sorry
