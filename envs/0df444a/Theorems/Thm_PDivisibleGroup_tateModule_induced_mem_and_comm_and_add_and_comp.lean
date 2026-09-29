-- Prove2me | Theorems.Thm_PDivisibleGroup_tateModule_induced_mem_and_comm_and_add_and_comp
-- name    : PDivisibleGroup.tateModule_induced_mem_and_comm_and_add_and_comp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:58.387243+00:00
-- url     : https://prove2.me/theorems/2e9fad35-2435-5f60-b806-0456368612df
-- title:
--   Tate-module endomorphisms induced by families of level endomorphisms
-- statement:
--   Fix a prime $p$, a commutative ring $O$ with a fixed $O$-algebra structure on $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ`, a valuation subring $P \subseteq \overline{\mathbb{Q}}$, and a $p$-divisible group $H$ of height $h$ over $O$ in the sense of the structure [`PDivisibleGroup`](def/PDivisibleGroup_Basic.html#L199): a system of levels `H.level v`, each a finite free cocommutative $O$-Hopf algebra of rank $p^{vh}$, together with surjective coalgebra maps `H.transition v` from level $v+1$ to level $v$ whose kernels are the prescribed torsion ideals. For a commutative $O$-algebra $L$, `H.Point L v` is the set of $O$-algebra maps `H.level v` $\to L$ with its convolution group law (`WithConv`), `H.Points L` is the direct limit of the groups `Additive (H.Point L v)`, with structure maps `H.pointsMkAdd L v` from level $v$, and $T :=$ [`TateModule p (H.Points L)`](def/EllipticCurve_TateModule.html#L15) is the group of sequences $x : \mathbb{N} \to$ `H.Points L` satisfying $p^n x_n = 0$ and $p\,x_{n+1} = x_n$ for all $n$, a $\mathbb{Z}_p$-module. Throughout, $L = \overline{\mathbb{Q}}$.
--
--   Let $S$ be a $\mathbb{Z}_p$-submodule of $T$, and let `hS` be the hypothesis that $S$ consists exactly of those $y \in T$ such that for every $n$ there are a level $w$ and a point $f \in$ `H.Point` $\overline{\mathbb{Q}}$ $w$ with `H.pointsMkAdd` $w$ $(\mathrm{ofMul}\,f) = y_n$ and with $P.\mathrm{valuation}\bigl(f(a) - \varepsilon(a)\cdot 1\bigr) < 1$ for every $a \in$ `H.level w`, where $f$ is viewed as an $O$-algebra map via [`PDivisibleGroup.Point.toAlgHom`](def/PDivisibleGroup_Points.html#L105) and $\varepsilon$ is the coalgebra counit; that is, $S$ is the set of Tate sequences all of whose components admit representatives congruent to the identity point modulo the maximal ideal of $P$.
--
--   Say that a $\mathbb{Z}_p$-linear endomorphism $U$ of $T$ is *induced by* a family $u = (u_w)_{w \in \mathbb{N}}$ of $O$-algebra endomorphisms $u_w$ of `H.level w` when the following holds: for all $x \in T$, all $n, w$ and all $f \in$ `H.Point` $\overline{\mathbb{Q}}$ $w$ with `H.pointsMkAdd` $w$ $(\mathrm{ofMul}\,f) = x_n$, the $n$-th component of $Ux$ equals the image under `H.pointsMkAdd` $w$ of the point obtained from the composite algebra map $f \circ u_w$ (written with [`PDivisibleGroup.Point.toAlgHom`](def/PDivisibleGroup_Points.html#L105), `AlgHom.comp` and [`PDivisibleGroup.Point.ofAlgHom`](def/PDivisibleGroup_Points.html#L107)). No compatibility of $u$ with the transition maps is required.
--
--   The conclusion is the conjunction of seven assertions.
--
--   1.
--
--   (Stability of $S$.) For every family $u$ and every $U$ induced by $u$ such that $u$ preserves the counit, i.e. $\varepsilon(u_w a) = \varepsilon(a)$ for all $w$ and all $a \in$ `H.level w`, one has $Uy \in S$ for every $y \in S$.
--
--   2.
--
--   (Galois equivariance.) For every family $u$ and every $U$ induced by $u$, and for every $O$-algebra automorphism $\tau'$ of $\overline{\mathbb{Q}}$, the endomorphisms `H.tateModuleRep` $\overline{\mathbb{Q}}$ $\tau'$ and $U$ of $T$ commute, where `H.tateModuleRep` is the action of $O$-algebra automorphisms of $\overline{\mathbb{Q}}$ on $T$ induced coefficientwise.
--
--   3.
--
--   (Addition.) For all families $u, u'$ and all $U, U'$ with $U$ induced by $u$ and $U'$ induced by $u'$, the endomorphism $U + U'$ is induced by the family $w \mapsto u_w * u'_w$, the convolution product taken in `WithConv`.
--
--   4.
--
--   (Composition.) For all families $u, u'$ and all $U, U'$ with $U$ induced by $u$ and $U'$ induced by $u'$, the composite $U \circ U'$ is induced by the family $w \mapsto u'_w \circ u_w$ (composition of algebra maps, $a \mapsto u'_w(u_w(a))$).
--
--   5.
--
--   (Identity.) The identity endomorphism $1$ of $T$ is induced by the family of identity algebra maps $w \mapsto \mathrm{id}_{H.\mathrm{level}\,w}$.
--
--   6.
--
--   (Zero.) The zero endomorphism of $T$ is induced by the family $w \mapsto$ (the counit algebra map `Bialgebra.counitAlgHom` of `H.level w` followed by `Algebra.ofId`), i.e. $a \mapsto \varepsilon(a)\cdot 1$, the neutral element for convolution.
--
--   7.
--
--   (Scalars.) For every family $u$, every $U$ induced by $u$ and every $c \in \mathbb{Z}_p$, the endomorphism $c \bullet U$ is induced by the family $w \mapsto u_w^{\,*\,\mathrm{appr}(c,w)}$, the convolution power of $u_w$ with exponent `PadicInt.appr c w`, the canonical natural-number approximation of $c$ modulo $p^w$.
--
--   This is the functoriality dictionary for Tate modules of $p$-divisible groups: it records that the relation "$U$ acts on representatives by precomposition with $u_w$" transports the ring operations and $\mathbb{Z}_p$-scalars from families of level endomorphisms to $\mathbb{Z}_p$-linear endomorphisms of the Tate module, that such $U$ are Galois-equivariant, and that counit-preserving families preserve the submodule of Tate sequences reducing to the identity point at the valuation subring $P$. It is used in the analysis of the Frobenius–Verschiebung relation on the Tate module and in the statement that all elements of the algebra generated by such endomorphisms preserve $S$ and commute with the Galois action.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PDivisibleGroup_tateModule_induced_mem_and_comm_and_add_and_comp.lean

import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_PDivisibleGroup_Points

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem PDivisibleGroup.tateModule_induced_mem_and_comm_and_add_and_comp
    (p : ℕ) [Fact p.Prime]
    {O : Type} [CommRing O] [Algebra O (AlgebraicClosure ℚ)]
    (P : ValuationSubring (AlgebraicClosure ℚ))
    {h : ℕ} (H : PDivisibleGroup O p h)
    (S : Submodule ℤ_[p] (TateModule p (H.Points (AlgebraicClosure ℚ))))
    (hS : ∀ y : TateModule p (H.Points (AlgebraicClosure ℚ)), y ∈ S ↔
        ∀ n : ℕ, ∃ (w : ℕ) (f : H.Point (AlgebraicClosure ℚ) w),
          H.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul f) =
            (y : ℕ → H.Points (AlgebraicClosure ℚ)) n ∧
          ∀ a : H.level w, P.valuation (PDivisibleGroup.Point.toAlgHom f a -
            algebraMap O (AlgebraicClosure ℚ) (Coalgebra.counit a)) < 1) :

    (∀ (u : ∀ w : ℕ, H.level w →ₐ[O] H.level w) (U : Module.End ℤ_[p] (TateModule p (H.Points (AlgebraicClosure ℚ)))),
      (∀ (x : TateModule p (H.Points (AlgebraicClosure ℚ))) (n w : ℕ) (f : H.Point (AlgebraicClosure ℚ) w),
        H.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul f) = (x : ℕ → H.Points (AlgebraicClosure ℚ)) n →
        ((U x : TateModule p (H.Points (AlgebraicClosure ℚ))) : ℕ → H.Points (AlgebraicClosure ℚ)) n =
          H.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
            ((PDivisibleGroup.Point.toAlgHom f).comp (u w))))) →
      (∀ (w : ℕ) (a : H.level w), Coalgebra.counit (R := O) (u w a) = Coalgebra.counit (R := O) a) →
      ∀ y : TateModule p (H.Points (AlgebraicClosure ℚ)), y ∈ S → U y ∈ S) ∧

    (∀ (u : ∀ w : ℕ, H.level w →ₐ[O] H.level w) (U : Module.End ℤ_[p] (TateModule p (H.Points (AlgebraicClosure ℚ)))),
      (∀ (x : TateModule p (H.Points (AlgebraicClosure ℚ))) (n w : ℕ) (f : H.Point (AlgebraicClosure ℚ) w),
        H.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul f) = (x : ℕ → H.Points (AlgebraicClosure ℚ)) n →
        ((U x : TateModule p (H.Points (AlgebraicClosure ℚ))) : ℕ → H.Points (AlgebraicClosure ℚ)) n =
          H.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
            ((PDivisibleGroup.Point.toAlgHom f).comp (u w))))) →
      ∀ τ' : AlgebraicClosure ℚ ≃ₐ[O] AlgebraicClosure ℚ,
        H.tateModuleRep (AlgebraicClosure ℚ) τ' ∘ₗ U = U ∘ₗ H.tateModuleRep (AlgebraicClosure ℚ) τ') ∧

    (∀ (u u' : ∀ w : ℕ, H.level w →ₐ[O] H.level w)
      (U U' : Module.End ℤ_[p] (TateModule p (H.Points (AlgebraicClosure ℚ)))),
      (∀ (x : TateModule p (H.Points (AlgebraicClosure ℚ))) (n w : ℕ) (f : H.Point (AlgebraicClosure ℚ) w),
        H.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul f) = (x : ℕ → H.Points (AlgebraicClosure ℚ)) n →
        ((U x : TateModule p (H.Points (AlgebraicClosure ℚ))) : ℕ → H.Points (AlgebraicClosure ℚ)) n =
          H.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
            ((PDivisibleGroup.Point.toAlgHom f).comp (u w))))) → (∀ (x : TateModule p (H.Points (AlgebraicClosure ℚ))) (n w : ℕ) (f : H.Point (AlgebraicClosure ℚ) w),
        H.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul f) = (x : ℕ → H.Points (AlgebraicClosure ℚ)) n →
        ((U' x : TateModule p (H.Points (AlgebraicClosure ℚ))) : ℕ → H.Points (AlgebraicClosure ℚ)) n =
          H.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
            ((PDivisibleGroup.Point.toAlgHom f).comp (u' w))))) →
      (∀ (x : TateModule p (H.Points (AlgebraicClosure ℚ))) (n w : ℕ) (f : H.Point (AlgebraicClosure ℚ) w),
        H.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul f) = (x : ℕ → H.Points (AlgebraicClosure ℚ)) n →
        (((U + U') x : TateModule p (H.Points (AlgebraicClosure ℚ))) : ℕ → H.Points (AlgebraicClosure ℚ)) n =
          H.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
            ((PDivisibleGroup.Point.toAlgHom f).comp ((fun w => (WithConv.toConv (u w) * WithConv.toConv (u' w)).ofConv) w)))))) ∧

    (∀ (u u' : ∀ w : ℕ, H.level w →ₐ[O] H.level w)
      (U U' : Module.End ℤ_[p] (TateModule p (H.Points (AlgebraicClosure ℚ)))),
      (∀ (x : TateModule p (H.Points (AlgebraicClosure ℚ))) (n w : ℕ) (f : H.Point (AlgebraicClosure ℚ) w),
        H.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul f) = (x : ℕ → H.Points (AlgebraicClosure ℚ)) n →
        ((U x : TateModule p (H.Points (AlgebraicClosure ℚ))) : ℕ → H.Points (AlgebraicClosure ℚ)) n =
          H.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
            ((PDivisibleGroup.Point.toAlgHom f).comp (u w))))) → (∀ (x : TateModule p (H.Points (AlgebraicClosure ℚ))) (n w : ℕ) (f : H.Point (AlgebraicClosure ℚ) w),
        H.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul f) = (x : ℕ → H.Points (AlgebraicClosure ℚ)) n →
        ((U' x : TateModule p (H.Points (AlgebraicClosure ℚ))) : ℕ → H.Points (AlgebraicClosure ℚ)) n =
          H.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
            ((PDivisibleGroup.Point.toAlgHom f).comp (u' w))))) →
      (∀ (x : TateModule p (H.Points (AlgebraicClosure ℚ))) (n w : ℕ) (f : H.Point (AlgebraicClosure ℚ) w),
        H.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul f) = (x : ℕ → H.Points (AlgebraicClosure ℚ)) n →
        (((U ∘ₗ U') x : TateModule p (H.Points (AlgebraicClosure ℚ))) : ℕ → H.Points (AlgebraicClosure ℚ)) n =
          H.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
            ((PDivisibleGroup.Point.toAlgHom f).comp ((fun w => (u' w).comp (u w)) w)))))) ∧

    (∀ (x : TateModule p (H.Points (AlgebraicClosure ℚ))) (n w : ℕ) (f : H.Point (AlgebraicClosure ℚ) w),
        H.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul f) = (x : ℕ → H.Points (AlgebraicClosure ℚ)) n →
        (((1 : Module.End ℤ_[p] (TateModule p (H.Points (AlgebraicClosure ℚ)))) x : TateModule p (H.Points (AlgebraicClosure ℚ))) : ℕ → H.Points (AlgebraicClosure ℚ)) n =
          H.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
            ((PDivisibleGroup.Point.toAlgHom f).comp ((fun w => AlgHom.id O (H.level w)) w))))) ∧
    (∀ (x : TateModule p (H.Points (AlgebraicClosure ℚ))) (n w : ℕ) (f : H.Point (AlgebraicClosure ℚ) w),
        H.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul f) = (x : ℕ → H.Points (AlgebraicClosure ℚ)) n →
        (((0 : Module.End ℤ_[p] (TateModule p (H.Points (AlgebraicClosure ℚ)))) x : TateModule p (H.Points (AlgebraicClosure ℚ))) : ℕ → H.Points (AlgebraicClosure ℚ)) n =
          H.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
            ((PDivisibleGroup.Point.toAlgHom f).comp ((fun w => (Algebra.ofId O (H.level w)).comp (Bialgebra.counitAlgHom O (H.level w))) w))))) ∧

    (∀ (u : ∀ w : ℕ, H.level w →ₐ[O] H.level w) (U : Module.End ℤ_[p] (TateModule p (H.Points (AlgebraicClosure ℚ)))),
      (∀ (x : TateModule p (H.Points (AlgebraicClosure ℚ))) (n w : ℕ) (f : H.Point (AlgebraicClosure ℚ) w),
        H.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul f) = (x : ℕ → H.Points (AlgebraicClosure ℚ)) n →
        ((U x : TateModule p (H.Points (AlgebraicClosure ℚ))) : ℕ → H.Points (AlgebraicClosure ℚ)) n =
          H.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
            ((PDivisibleGroup.Point.toAlgHom f).comp (u w))))) →
      ∀ c : ℤ_[p], (∀ (x : TateModule p (H.Points (AlgebraicClosure ℚ))) (n w : ℕ) (f : H.Point (AlgebraicClosure ℚ) w),
        H.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul f) = (x : ℕ → H.Points (AlgebraicClosure ℚ)) n →
        (((c • U) x : TateModule p (H.Points (AlgebraicClosure ℚ))) : ℕ → H.Points (AlgebraicClosure ℚ)) n =
          H.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
            ((PDivisibleGroup.Point.toAlgHom f).comp ((fun w => (WithConv.toConv (u w) ^ PadicInt.appr c w).ofConv) w)))))) := by sorry
