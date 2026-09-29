-- Prove2me | Theorems.Thm_WeierstrassCurve_natCard_isAddCyclic_addSubgroup_card_eq_fixed_vcInvFun_eq_nuThree
-- name    : WeierstrassCurve.natCard_isAddCyclic_addSubgroup_card_eq_fixed_vcInvFun_eq_nuThree
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/d6495b5f-be77-5f82-a6d2-899d7829bc29
-- title:
--   Cyclic N-subgroups of y²=x³+B stable under [ω]
-- statement:
--   Let $L$ be an algebraically closed field equipped with a $\mathbb{Q}$-algebra structure (so of characteristic $0$), let $B \in L$ with $B \neq 0$, let $u \in L^{\times}$ satisfy $u^{3} = 1$ and $u \neq 1$, and let $N$ be a nonzero natural number. Write $W$ for the Weierstrass curve with coefficients $(a_1,a_2,a_3,a_4,a_6) = (0,0,0,0,B)$, i.e. $y^{2} = x^{3} + B$, and consider its affine point group $W_{\mathrm{aff}}(L)$ (the nonsingular affine points together with the point at infinity). For the variable change $C = (u,0,0,0)$, the transport map `Point.vcInvFun` sends the point at infinity to the point at infinity and a point $(x,y)$ to the point with coordinates $(u^{-2}(x-0),\; u^{-3}(y-0-0\cdot(x-0))) = (u^{-2}x, u^{-3}y)$ on the curve $C \bullet W$. The assertion is that the number of additive subgroups $H \le W_{\mathrm{aff}}(L)$ which are additively cyclic, satisfy $\#H = N$, and are stable under this transport in the sense that for every $T \in H$ there exists $T' \in H$ with `HEq (Point.vcInvFun C W.toAffine T) T'` (heterogeneous equality, the source and target groups being those of $C \bullet W$ and of $W$), equals `nuThree N`, the number of $x \in \mathbb{Z}/N$ with $x^{2} + x + 1 = 0$.
--
--   This is the "fixed" contribution in the count of elliptic points of order $3$ on the modular curve $Y_0(N)$: cyclic subgroups of order $N$ on a curve with $j = 0$ that are carried to themselves by the automorphism $(x,y) \mapsto (\omega x, y)$ of order $3$. It is used by [`ModularCurve.three_mul_natCard_moduliPoint_j_eq_zero_eq_dedekindPsi_add_two_mul_nuThree`](thm.html#ModularCurve.three_mul_natCard_moduliPoint_j_eq_zero_eq_dedekindPsi_add_two_mul_nuThree), which assembles the double count of such moduli points into the formula involving the Dedekind $\psi$-function and $\nu_3(N)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_natCard_isAddCyclic_addSubgroup_card_eq_fixed_vcInvFun_eq_nuThree.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Definitions.Def_ModularCurve_GenusNumerics

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine ModularCurve

theorem WeierstrassCurve.natCard_isAddCyclic_addSubgroup_card_eq_fixed_vcInvFun_eq_nuThree
    {L : Type*} [Field L] [DecidableEq L] [Algebra ℚ L] [IsAlgClosed L]
    (B : L) (hB : B ≠ 0) (u : Lˣ) (hu : (u : L) ^ 3 = 1) (hu1 : (u : L) ≠ 1) (N : ℕ) (hN : N ≠ 0) :
    Nat.card {H : AddSubgroup (⟨0, 0, 0, 0, B⟩ : WeierstrassCurve L).toAffine.Point //
        IsAddCyclic H ∧ Nat.card H = N ∧
        ∀ T ∈ H, ∃ T' ∈ H, HEq (Point.vcInvFun (⟨u, 0, 0, 0⟩ : VariableChange L)
          (⟨0, 0, 0, 0, B⟩ : WeierstrassCurve L).toAffine T) T'}
      = nuThree N := by sorry
