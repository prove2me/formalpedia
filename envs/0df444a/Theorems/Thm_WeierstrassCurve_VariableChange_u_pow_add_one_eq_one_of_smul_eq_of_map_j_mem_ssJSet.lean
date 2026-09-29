-- Prove2me | Theorems.Thm_WeierstrassCurve_VariableChange_u_pow_add_one_eq_one_of_smul_eq_of_map_j_mem_ssJSet
-- name    : WeierstrassCurve.VariableChange.u_pow_add_one_eq_one_of_smul_eq_of_map_j_mem_ssJSet
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/82767916-8eab-5977-8ffe-cad3ba550024
-- title:
--   Supersingular j forces u^{q+1}=1 for stabilising variable changes
-- statement:
--   Let $q$ be a prime with $q\ge 5$, let $k$ be a field of characteristic $q$ and let $W$ be a Weierstrass curve over $k$ which is elliptic (invertible discriminant). Let $\Omega$ be an algebraically closed field of characteristic $q$ with decidable equality, and let $\iota : k \to \Omega$ be a ring homomorphism. Assume that $\iota(j(W))$ lies in $\mathrm{ssJSet}\ q\ \Omega$, that is: every elliptic Weierstrass curve $W'$ over $\Omega$ whose $j$-invariant equals $\iota(j(W))$ has no nontrivial $q$-torsion among the points of its associated affine curve, every $P$ with $q \cdot P = 0$ being $0$. Finally let $C = (u,r,s,t)$ be a variable change over $k$, with $u$ a unit of $k$, acting trivially on $W$, i.e. $C \bullet W = W$. The conclusion is that the scaling factor satisfies $u^{q+1} = 1$ in $k$.
--
--   The statement records the standard fact that an automorphism of a supersingular Weierstrass model in characteristic $q\ge 5$ has scaling factor a root of unity of order dividing $q+1$; the hypothesis of supersingularity is essential, since an ordinary curve with $j = 1728$ and $q \equiv 1 \pmod 4$ has automorphisms of order $4 \nmid q+1$. It feeds the comparison of moduli-theoretic group actions used in [`ModularCurve.LevelModuliPackageAbs.u_pow_sub_one_mem_and_of_act_mapRing_eq_relabel_gamma0Pow_of_mem_ssJSet`](thm.html#ModularCurve.LevelModuliPackageAbs.u_pow_sub_one_mem_and_of_act_mapRing_eq_relabel_gamma0Pow_of_mem_ssJSet).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_VariableChange_u_pow_add_one_eq_one_of_smul_eq_of_map_j_mem_ssJSet.lean

import Mathlib
import Definitions.Def_ModularCurve_SupersingularModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem WeierstrassCurve.VariableChange.u_pow_add_one_eq_one_of_smul_eq_of_map_j_mem_ssJSet
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q)
    (k : Type) [Field k] [CharP k q] (W : WeierstrassCurve k) [W.IsElliptic]
    (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω] (ι : k →+* Ω)
    (hss : ι W.j ∈ ModularCurve.ssJSet q Ω)
    (C : WeierstrassCurve.VariableChange k) (hC : C • W = W) :
    (C.u : k) ^ (q + 1) = 1 := by sorry
