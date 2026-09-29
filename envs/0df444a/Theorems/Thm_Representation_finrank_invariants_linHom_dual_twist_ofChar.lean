-- Prove2me | Theorems.Thm_Representation_finrank_invariants_linHom_dual_twist_ofChar
-- name    : Representation.finrank_invariants_linHom_dual_twist_ofChar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:01.535489+00:00
-- url     : https://prove2.me/theorems/7e500683-8e9e-5cc1-9d54-f2bd628b11fb
-- title:
--   Dimension of Hom_Δ(V^∨(χ),k(χ)) equals dim V^Δ
-- statement:
--   Let $k$ be a field, $\Delta$ a group and $V$ a finite-dimensional $k$-vector space carrying a representation $\rho$ of $\Delta$, and let $\chi : \Delta \to k^{\times}$ be a multiplicative character. Form two representations of $\Delta$: first the twist by $\chi$ of the dual (contragredient) representation $\rho^{\vee}$, i.e. the action on $\mathrm{Hom}_k(V,k)$ given by $g \mapsto (\chi(g) : k) \cdot {}^{t}\rho(g^{-1})$, so $f \mapsto \chi(g)\,(f \circ \rho(g^{-1}))$; and second the twist by $\chi$ of the trivial representation of $\Delta$ on $k$, i.e. the character line on which $g$ acts as multiplication by $\chi(g)$, where in both cases the twist of a representation $\sigma$ by $\chi$ is by definition $g \mapsto (\chi(g):k)\cdot \sigma(g)$. The assertion is that the space of $\Delta$-invariants in the representation on $k$-linear maps $\mathrm{Hom}_k(\mathrm{Hom}_k(V,k),k)$ induced by these two (with $g$ acting by $\varphi \mapsto \sigma_2(g)\circ \varphi \circ \sigma_1(g^{-1})$) has the same $k$-dimension as the space of $\rho$-invariants in $V$: $\dim_k \mathrm{Hom}_\Delta(V^{\vee}(\chi), k(\chi)) = \dim_k V^{\Delta}$.
--
--   This is the elementary dimension count identifying equivariant maps from a twisted dual into the corresponding character line with the invariants of the original representation; the twisting character cancels, so no hypothesis on $\chi$ is needed. It feeds a local dimension formula for continuous $H^1$ in the tame setting, [`groupCohomology.finrank_continuousH1_eq_invariants_add_dualTwist_add_finrank_mul_of_tame_intermediateField`](thm.html#groupCohomology.finrank_continuousH1_eq_invariants_add_dualTwist_add_finrank_mul_of_tame_intermediateField).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Representation_finrank_invariants_linHom_dual_twist_ofChar.lean

import Mathlib
import Definitions.Def_GroupCohomology_Selmer

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u
open Module

theorem Representation.finrank_invariants_linHom_dual_twist_ofChar
    {k : Type*} [Field k] {Δ : Type*} [Group Δ]
    {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V] (ρ : Representation k Δ V) (χ : Δ →* kˣ) :
    finrank k ((ρ.dual.twist χ).linHom ((Representation.trivial k Δ k).twist χ)).invariants = finrank k ρ.invariants := by sorry
