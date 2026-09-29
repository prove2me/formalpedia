-- Prove2me | Theorems.Thm_PDivisibleGroup_Hopf_exists_forall_comp_transition_surjective_ker_eq_torsionIdeal
-- name    : PDivisibleGroup.Hopf.exists_forall_comp_transition_surjective_ker_eq_torsionIdeal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:58.387243+00:00
-- url     : https://prove2.me/theorems/61d763c5-d22d-5341-ab64-d7945fa59bdf
-- title:
--   Iterated transitions in a p-divisible tower of Hopf algebras
-- statement:
--   Let $\mathcal O$ be a commutative ring and $p,h$ natural numbers. Let $L : \mathbb N \to \mathrm{Type}$ be a family of commutative rings, each carrying a Hopf algebra structure over $\mathcal O$ with cocommutative comultiplication and free and finite as an $\mathcal O$-module, and let $t_v : L(v+1) \to L(v)$ be bialgebra maps over $\mathcal O$ that are surjective, with $\operatorname{finrank}_{\mathcal O} L(v) = p^{v h}$ and $\ker t_v$ equal to the $p^v$-torsion ideal of $L(v+1)$, i.e. the image under the $p^v$-th convolution power of the identity of the augmentation ideal $\ker \varepsilon$. Then there is a family of $\mathcal O$-bialgebra maps $T_{v,w} : L(v+w) \to L(v)$ such that: $T_{v,0}$ is the identity; $T_{v,w+1}$ is $t_{v+w}$ followed by $T_{v,w}$; each $T_{v,w}$ is surjective; $\ker T_{v,w}$ is the $p^v$-torsion ideal of $L(v+w)$; for every $v$ the algebra endomorphism $[p^v]$ of $L(v)$ (the $p^v$-th convolution power of the identity) equals the counit of $L(v)$ followed by the structure map $\mathcal O \to L(v)$; and for all $v,w$ the quotient of $L(v+w)$ by its $p^w$-torsion ideal is a free $\mathcal O$-module of rank $p^{w h}$.
--
--   These are the elementary two-level consequences of Tate's axioms for a $p$-divisible group, stated for a tower of coordinate rings presented explicitly rather than as a bundled structure: the identification $\Gamma_v = \Gamma_{v+w}[p^v]$ for all $w$, the fact that each level is killed by its order, and freeness of rank $p^{wh}$ for $\Gamma_{v+w}[p^w]$. It is used wherever two levels of a tower must be compared, for instance in the construction of $p$-divisible towers from formal groups and from Honda systems, and in reducedness statements for Cartier duals.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PDivisibleGroup_Hopf_exists_forall_comp_transition_surjective_ker_eq_torsionIdeal.lean

import Mathlib
import Definitions.Def_PDivisibleGroup_Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v

theorem PDivisibleGroup.Hopf.exists_forall_comp_transition_surjective_ker_eq_torsionIdeal
    {𝓞 : Type u} [CommRing 𝓞] (p h : ℕ)
    (L : ℕ → Type v) [∀ v, CommRing (L v)] [∀ v, HopfAlgebra 𝓞 (L v)]
    [∀ v, Coalgebra.IsCocomm 𝓞 (L v)] [∀ v, Module.Free 𝓞 (L v)] [∀ v, Module.Finite 𝓞 (L v)]
    (t : ∀ v, L (v + 1) →ₐc[𝓞] L v) (ht : ∀ v, Function.Surjective (t v))
    (hrankL : ∀ v, Module.finrank 𝓞 (L v) = p ^ (v * h))
    (hkerL : ∀ v, RingHom.ker (t v) = PDivisibleGroup.Hopf.torsionIdeal 𝓞 (L (v + 1)) (p ^ v)) :
    ∃ T : ∀ v w : ℕ, L (v + w) →ₐc[𝓞] L v,
      (∀ v, T v 0 = BialgHom.id 𝓞 (L v)) ∧
      (∀ v w, T v (w + 1) = (T v w).comp (t (v + w))) ∧
      (∀ v w, Function.Surjective (T v w)) ∧
      (∀ v w, RingHom.ker (T v w) = PDivisibleGroup.Hopf.torsionIdeal 𝓞 (L (v + w)) (p ^ v)) ∧
      (∀ v, PDivisibleGroup.Hopf.nsmulAlgHom 𝓞 (L v) (p ^ v) =
        (Algebra.ofId 𝓞 (L v)).comp (Bialgebra.counitAlgHom 𝓞 (L v))) ∧
      (∀ v w, Module.Free 𝓞 (L (v + w) ⧸ PDivisibleGroup.Hopf.torsionIdeal 𝓞 (L (v + w)) (p ^ w)) ∧
        Module.finrank 𝓞 (L (v + w) ⧸ PDivisibleGroup.Hopf.torsionIdeal 𝓞 (L (v + w)) (p ^ w)) =
          p ^ (w * h)) := by sorry
