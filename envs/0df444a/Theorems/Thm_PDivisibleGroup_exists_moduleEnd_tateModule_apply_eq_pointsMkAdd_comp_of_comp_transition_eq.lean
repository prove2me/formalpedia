-- Prove2me | Theorems.Thm_PDivisibleGroup_exists_moduleEnd_tateModule_apply_eq_pointsMkAdd_comp_of_comp_transition_eq
-- name    : PDivisibleGroup.exists_moduleEnd_tateModule_apply_eq_pointsMkAdd_comp_of_comp_transition_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:58.387243+00:00
-- url     : https://prove2.me/theorems/6f578dca-a7a4-5552-82e7-cb9067edd6a5
-- title:
--   Transition-compatible level endomorphisms induce a Tate-module endomorphism
-- statement:
--   Let $p$ be a prime, $O$ a commutative ring, $L$ a commutative $O$-algebra, $h$ a natural number, and let $G$ be a $p$-divisible group of height $h$ over $O$ in the sense of the structure [`PDivisibleGroup`](def/PDivisibleGroup_Basic.html#L199): a system of levels $G_v =$ `G.level v`, each a commutative ring that is a cocommutative Hopf $O$-algebra, finite and free as an $O$-module of rank $p^{vh}$, together with surjective bialgebra transition maps $G_{v+1} \to G_v$ whose kernels are the prescribed torsion ideals. Let $u_v : G_v \to G_v$ be bialgebra endomorphisms, one for each $v$, satisfying the compatibility $\mathrm{transition}_v \circ u_{v+1} = u_v \circ \mathrm{transition}_v$ for every $v$. Write $G(L)$ for `G.Points L`, the direct limit of the additive groups $\mathrm{Additive}(G_v \to_{O\text{-alg}} L)$ (algebra homomorphisms under convolution) along the inclusion maps, with $\mathrm{pointsMkAdd}$ the canonical maps from level $v$. Then there is a $\mathbb{Z}_p$-linear endomorphism $U$ of $\mathrm{TateModule}\, p\, (G(L))$ — the group of sequences $(x_n)_{n \in \mathbb{N}}$ in $G(L)$ with $p^n x_n = 0$ and $p\, x_{n+1} = x_n$ — such that for every such $x$, every $n$ and $w$, and every $f : G_w \to L$ whose class at level $w$ equals $x_n$, the $n$-th component of $U x$ is the class at level $w$ of the algebra homomorphism $u_w$ followed by $f$.
--
--   This is the functoriality of the Tate module of a $p$-divisible group in a transition-compatible family of endomorphisms of its levels: the family $u$ produces an operator on $T_p(G(L))$ described on representatives. It supplies the operator assumed in the statements about Hecke and Frobenius actions on corner submodules of Tate modules of modular curves, such as [`ModularCurve.exists_bialgHom_family_idempotent_inverse_U_of_cornerIdempotent_tateModule_jH`](thm.html#ModularCurve.exists_bialgHom_family_idempotent_inverse_U_of_cornerIdempotent_tateModule_jH) and the ordinary-case slope statements that cite it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PDivisibleGroup_exists_moduleEnd_tateModule_apply_eq_pointsMkAdd_comp_of_comp_transition_eq.lean

import Mathlib
import Definitions.Def_PDivisibleGroup_Points

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem PDivisibleGroup.exists_moduleEnd_tateModule_apply_eq_pointsMkAdd_comp_of_comp_transition_eq
    (p : ℕ) [Fact p.Prime] {O : Type} [CommRing O] {L : Type} [CommRing L] [Algebra O L]
    {h : ℕ} (G : PDivisibleGroup O p h)
    (u : ∀ v : ℕ, G.level v →ₐc[O] G.level v)
    (hu : ∀ v : ℕ, (G.transition v).comp (u (v + 1)) = (u v).comp (G.transition v)) :
    ∃ U : Module.End ℤ_[p] (TateModule p (G.Points L)),
      ∀ (x : TateModule p (G.Points L)) (n w : ℕ) (f : G.Point L w),
        G.pointsMkAdd L w (Additive.ofMul f) = (x : ℕ → G.Points L) n →
        ((U x : TateModule p (G.Points L)) : ℕ → G.Points L) n =
          G.pointsMkAdd L w (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
            ((PDivisibleGroup.Point.toAlgHom f).comp (u w : G.level w →ₐ[O] G.level w)))) := by sorry
