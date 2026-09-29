-- Prove2me | Theorems.Thm_WeierstrassCurve_natCard_fibre_dvd_jWidth_of_variableChange_orbitMap
-- name    : WeierstrassCurve.natCard_fibre_dvd_jWidth_of_variableChange_orbitMap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/c33ddd0d-6f7b-58f9-a43e-956a3f4d8671
-- title:
--   Fibres of an orbit map on cyclic N-subgroups divide the j-width
-- statement:
--   Let $K$ be an algebraically closed field with $\operatorname{char} K \neq 2, 3$, let $W$ be a Weierstrass curve over $K$ which is elliptic, and let $N$ be a nonzero natural number. Write $X$ for the type of additive subgroups $H$ of the group $W.\mathrm{toAffine}.\mathrm{Point}$ of affine points of $W$ that are additively cyclic and satisfy $\mathrm{Nat.card}\,H = N$. Let $\alpha$ be any type and $f : X \to \alpha$ any map with the property that for all $H, H' \in X$ one has $f(H) = f(H')$ if and only if there is an admissible change of variables $\gamma = (u, r, s, t)$ over $K$ with $\gamma \bullet W = W$ such that every $T \in H$ satisfies: some $T' \in H'$ is heterogeneously equal to $\mathrm{Point.vcInvFun}\,\gamma\,W.\mathrm{toAffine}\,T$, the point of $(\gamma \bullet W).\mathrm{toAffine}$ obtained by sending $0 \mapsto 0$ and $(x,y) \mapsto (u^{-2}(x-r),\, u^{-3}(y-t-s(x-r)))$. Then for every $H \in X$, the number of $H' \in X$ with $f(H') = f(H)$ divides $\mathrm{ModularCurve.jWidth}\,(j(W))$, which is $3$ if $j(W) = 0$, $2$ if $j(W) = 1728$, and $1$ otherwise.
--
--   This is the orbit-map form of the statement that a fibre of the natural map from cyclic $N$-subgroups of an elliptic curve to their automorphism orbits has size dividing the ramification weight $e(j) \in \{1,2,3\}$ at $j$; it rests on the order $2e(j)$ of the group of variable changes fixing $W$ together with the fact that $[-1]$ preserves every subgroup. It is used in the modular interpretation of the fibres of $j$ on $X_0(N)$, notably by [`ModularCurve.placeRamificationJ_dvd_jWidth_of_mem_ssPlaces`](thm.html#ModularCurve.placeRamificationJ_dvd_jWidth_of_mem_ssPlaces) and the associated statements about ramification of $j$ at places of the modular function field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_natCard_fibre_dvd_jWidth_of_variableChange_orbitMap.lean

import Mathlib
import Definitions.Def_ModularCurve_JWidth
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine

theorem WeierstrassCurve.natCard_fibre_dvd_jWidth_of_variableChange_orbitMap
    {K : Type*} [Field K] [IsAlgClosed K] [DecidableEq K]
    (h2 : ringChar K ≠ 2) (h3 : ringChar K ≠ 3)
    (W : WeierstrassCurve K) [W.IsElliptic] (N : ℕ) [NeZero N] {α : Type*}
    (f : {H : AddSubgroup W.toAffine.Point // IsAddCyclic H ∧ Nat.card H = N} → α)
    (hf : ∀ H H', f H = f H' ↔ ∃ γ : VariableChange K, γ • W = W ∧
      ∀ T ∈ H.1, ∃ T' ∈ H'.1, HEq (Point.vcInvFun γ W.toAffine T) T')
    (H : {H : AddSubgroup W.toAffine.Point // IsAddCyclic H ∧ Nat.card H = N}) :
    Nat.card {H' : {H : AddSubgroup W.toAffine.Point // IsAddCyclic H ∧ Nat.card H = N} //
        f H' = f H} ∣ ModularCurve.jWidth W.j := by sorry
