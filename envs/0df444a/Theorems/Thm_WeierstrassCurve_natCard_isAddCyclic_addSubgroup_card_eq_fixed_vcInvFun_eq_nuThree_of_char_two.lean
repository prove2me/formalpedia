-- Prove2me | Theorems.Thm_WeierstrassCurve_natCard_isAddCyclic_addSubgroup_card_eq_fixed_vcInvFun_eq_nuThree_of_char_two
-- name    : WeierstrassCurve.natCard_isAddCyclic_addSubgroup_card_eq_fixed_vcInvFun_eq_nuThree_of_char_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/b7f1fdbe-e6d2-5d99-a44b-78f03d1fe268
-- title:
--   [ω]-stable cyclic N-subgroups of y²+y=x³ in characteristic 2
-- statement:
--   Let $L$ be an algebraically closed field of characteristic $2$, let $u \in L^\times$ satisfy $u^3 = 1$ and $u \neq 1$ (a primitive cube root of unity), and let $N$ be a natural number whose image in $L$ is non-zero, i.e. $N$ is odd (in particular $N \neq 0$). Write $E_0$ for the affine Weierstrass curve over $L$ with coefficients $(a_1,a_2,a_3,a_4,a_6) = (0,0,1,0,0)$, that is $y^2 + y = x^3$, and let $C = (u,0,0,0)$ be the variable change with scaling unit $u$ and $r = s = t = 0$. The assertion is that the number of additive subgroups $H$ of the group $E_0(L)$ of affine points such that $H$ is additively cyclic, $\operatorname{card} H = N$, and every $T \in H$ has its image under `Point.vcInvFun` for $C$ again in $H$ — the image being the point $(u^{-2}(x - 0),\, u^{-3}(y - 0 - 0\cdot(x-0))) = (u^{-2}x, u^{-3}y)$ for $T = (x,y)$, and $0$ for $T = 0$, with membership expressed by heterogeneous equality since `vcInvFun` takes values in the point group of the transformed curve $C \bullet E_0$ — equals $\nu_3(N) = \operatorname{card}\{x \in \mathbb{Z}/N\mathbb{Z} : x^2 + x + 1 = 0\}$.
--
--   This is the characteristic-$2$ counterpart of the count of cyclic $N$-subgroups stable under the order-three automorphism $[\omega]$ of a curve with $j$-invariant $0$: here $E_0 : y^2+y=x^3$ is the supersingular curve in characteristic $2$ and $[\omega]$ is induced by the variable change $(u,0,0,0)$, so that $(x,y) \mapsto (ux,y)$. It feeds the counts of elliptic points and of supersingular points used in the genus and census computations for modular curves, being cited by [`ModularCurve.card_eq_ssCountFormula_of_ssPlaces_of_lt_five`](thm.html#ModularCurve.card_eq_ssCountFormula_of_ssPlaces_of_lt_five) and [`ModularCurve.ord_jqModC_census_of_char_two`](thm.html#ModularCurve.ord_jqModC_census_of_char_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_natCard_isAddCyclic_addSubgroup_card_eq_fixed_vcInvFun_eq_nuThree_of_char_two.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Definitions.Def_ModularCurve_GenusNumerics

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine ModularCurve

theorem WeierstrassCurve.natCard_isAddCyclic_addSubgroup_card_eq_fixed_vcInvFun_eq_nuThree_of_char_two
    {L : Type*} [Field L] [DecidableEq L] [IsAlgClosed L] [CharP L 2]
    (u : Lˣ) (hu : (u : L) ^ 3 = 1) (hu1 : (u : L) ≠ 1) (N : ℕ) (hN : (N : L) ≠ 0) :
    Nat.card {H : AddSubgroup (⟨0, 0, 1, 0, 0⟩ : WeierstrassCurve L).toAffine.Point //
        IsAddCyclic H ∧ Nat.card H = N ∧
        ∀ T ∈ H, ∃ T' ∈ H, HEq (Point.vcInvFun (⟨u, 0, 0, 0⟩ : VariableChange L)
          (⟨0, 0, 1, 0, 0⟩ : WeierstrassCurve L).toAffine T) T'}
      = nuThree N := by sorry
