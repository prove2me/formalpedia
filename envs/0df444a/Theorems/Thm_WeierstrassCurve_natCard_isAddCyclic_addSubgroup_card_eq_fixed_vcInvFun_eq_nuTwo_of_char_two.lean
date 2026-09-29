-- Prove2me | Theorems.Thm_WeierstrassCurve_natCard_isAddCyclic_addSubgroup_card_eq_fixed_vcInvFun_eq_nuTwo_of_char_two
-- name    : WeierstrassCurve.natCard_isAddCyclic_addSubgroup_card_eq_fixed_vcInvFun_eq_nuTwo_of_char_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/ef7b5c55-49d5-5e63-a573-defa7be93e16
-- title:
--   Counting [i]-stable cyclic N-subgroups of y²+y=x³ in characteristic 2
-- statement:
--   Let $L$ be an algebraically closed field of characteristic $2$, let $\omega \in L$ satisfy $\omega^2 + \omega + 1 = 0$, and let $N$ be a natural number whose image in $L$ is nonzero (equivalently, $N$ is odd). Consider the Weierstrass curve with coefficients $(a_1,a_2,a_3,a_4,a_6) = (0,0,1,0,0)$, that is $y^2 + y = x^3$, over $L$, and its group of affine points. Count the additive subgroups $H$ of this group that are cyclic, have cardinality exactly $N$, and satisfy the following stability property: for every $T \in H$ there is $T' \in H$ with the image of $T$ under `Point.vcInvFun` for the variable change $(u,r,s,t) = (1,1,1,\omega)$ heterogeneously equal to $T'$ — here that image of a point $(x,y)$ is the point with coordinates $u^{-2}(x-r) = x+1$ and $u^{-3}(y-t-s(x-r)) = y + x + \omega + 1$ on the transformed curve, and the point at infinity goes to the point at infinity. The assertion is that the number of such $H$ equals $\nu_2(N)$, defined as the number of $x \in \mathbb{Z}/N\mathbb{Z}$ with $x^2 + 1 = 0$.
--
--   The curve $y^2 + y = x^3$ is the supersingular elliptic curve in characteristic $2$ with $j = 0$, and the variable change $(1,1,1,\omega)$ induces on its points the order-four automorphism $[i]\colon (x,y) \mapsto (x+1, y+x+\omega+1)$ whose square is negation; the count of $[i]$-stable cyclic subgroups of order $N$ matches the number of square roots of $-1$ modulo $N$, exactly as in the classical count of elliptic points of order $2$ on modular curves. It is used in the characteristic-$2$ supersingular bookkeeping for modular curves, by [`ModularCurve.card_eq_ssCountFormula_of_ssPlaces_of_lt_five`](thm.html#ModularCurve.card_eq_ssCountFormula_of_ssPlaces_of_lt_five) and [`ModularCurve.ord_jqModC_census_of_char_two`](thm.html#ModularCurve.ord_jqModC_census_of_char_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_natCard_isAddCyclic_addSubgroup_card_eq_fixed_vcInvFun_eq_nuTwo_of_char_two.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Definitions.Def_ModularCurve_GenusNumerics

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine ModularCurve

theorem WeierstrassCurve.natCard_isAddCyclic_addSubgroup_card_eq_fixed_vcInvFun_eq_nuTwo_of_char_two
    {L : Type*} [Field L] [DecidableEq L] [IsAlgClosed L] [CharP L 2]
    (ω : L) (hω : ω ^ 2 + ω + 1 = 0) (N : ℕ) (hN : (N : L) ≠ 0) :
    Nat.card {H : AddSubgroup (⟨0, 0, 1, 0, 0⟩ : WeierstrassCurve L).toAffine.Point //
        IsAddCyclic H ∧ Nat.card H = N ∧
        ∀ T ∈ H, ∃ T' ∈ H, HEq (Point.vcInvFun (⟨1, 1, 1, ω⟩ : VariableChange L)
          (⟨0, 0, 1, 0, 0⟩ : WeierstrassCurve L).toAffine T) T'}
      = nuTwo N := by sorry
