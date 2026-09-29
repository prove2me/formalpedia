-- Prove2me | Theorems.Thm_PDivisibleGroup_eq_of_forall_toAlgHom_comp_eq_of_ringOfIntegers
-- name    : PDivisibleGroup.eq_of_forall_toAlgHom_comp_eq_of_ringOfIntegers
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:58.387243+00:00
-- url     : https://prove2.me/theorems/b2d835ad-9d50-5a6c-9d8a-36a4c1df2ad2
-- title:
--   Geometric points determine bialgebra maps of p-divisible groups
-- statement:
--   Fix a prime $p$ and an intermediate field $K$ of $\overline{\mathbb{Q}}_p/\mathbb{Q}_p$ (here $\overline{\mathbb{Q}}_p$ is `PadicAlgCl p`) with $K$ finite-dimensional over $\mathbb{Q}_p$, and let $\mathcal{O}_K =$ [`PadicAlgCl.ringOfIntegers p K`](def/PadicAlgCl_RingOfIntegers.html#L11) be the $\mathbb{Z}_p$-subalgebra of $\overline{\mathbb{Q}}_p$ obtained as the intersection of the integral closure of $\mathbb{Z}_p$ in $\overline{\mathbb{Q}}_p$ with $K$. Let $G$ and $H$ be $p$-divisible groups over $\mathcal{O}_K$ of heights $h$ and $h'$ in the sense of [`PDivisibleGroup`](def/PDivisibleGroup_Basic.html#L199): each consists of a family of levels `level v` ($v\in\mathbb{N}$) that are commutative rings, cocommutative Hopf algebras over $\mathcal{O}_K$, finite and free as $\mathcal{O}_K$-modules with $\operatorname{rank} = p^{vh}$, together with surjective bialgebra transition maps `level (v+1) → level v` whose kernels are the $p^v$-torsion ideals. Let $\varphi, \varphi'$ be two families of $\mathcal{O}_K$-bialgebra homomorphisms $\varphi_v, \varphi'_v : H.\mathrm{level}\,v \to G.\mathrm{level}\,v$. Assume that for every level $v$ and every point $x$ of $G$ of level $v$ with values in $\overline{\mathbb{Q}}_p$ — that is, every $\mathcal{O}_K$-algebra homomorphism $G.\mathrm{level}\,v \to \overline{\mathbb{Q}}_p$, viewed as an element of the convolution monoid — the two composites of $\varphi_v$, resp. $\varphi'_v$, with the algebra homomorphism underlying $x$ coincide. The conclusion is that $\varphi = \varphi'$ as families of bialgebra homomorphisms.
--
--   This is the uniqueness half of Tate's full faithfulness statement for $p$-divisible groups over the ring of integers of a finite extension of $\mathbb{Q}_p$: a morphism of the level Hopf algebras is determined by its effect on $\overline{\mathbb{Q}}_p$-valued points. It is used by [`PDivisibleGroup.existsUnique_bialgHom_family_of_addMonoidHom_points_levelPreserving_galois_of_ringOfIntegers`](thm.html#PDivisibleGroup.existsUnique_bialgHom_family_of_addMonoidHom_points_levelPreserving_galois_of_ringOfIntegers), which supplies the corresponding existence statement.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PDivisibleGroup_eq_of_forall_toAlgHom_comp_eq_of_ringOfIntegers.lean

import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_PDivisibleGroup_Dimension
import Definitions.Def_PadicAlgCl_RingOfIntegers

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem PDivisibleGroup.eq_of_forall_toAlgHom_comp_eq_of_ringOfIntegers
    (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    {h h' : ℕ} (G : PDivisibleGroup (PadicAlgCl.ringOfIntegers p K) p h)
    (H : PDivisibleGroup (PadicAlgCl.ringOfIntegers p K) p h')
    (φ φ' : ∀ v : ℕ, H.level v →ₐc[PadicAlgCl.ringOfIntegers p K] G.level v)
    (hφ : ∀ (v : ℕ) (x : G.Point (PadicAlgCl p) v),
      (PDivisibleGroup.Point.toAlgHom x).comp (φ v : H.level v →ₐ[PadicAlgCl.ringOfIntegers p K] G.level v) =
        (PDivisibleGroup.Point.toAlgHom x).comp (φ' v : H.level v →ₐ[PadicAlgCl.ringOfIntegers p K] G.level v)) :
    φ = φ' := by sorry
