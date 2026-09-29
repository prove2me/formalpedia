-- Prove2me | Theorems.Thm_PDivisibleGroup_eq_of_hasDimension_of_linearEquiv_tateModule_of_ringOfIntegers
-- name    : PDivisibleGroup.eq_of_hasDimension_of_linearEquiv_tateModule_of_ringOfIntegers
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:58.387243+00:00
-- url     : https://prove2.me/theorems/d28d0060-b24c-55d1-9ede-bb5c1a92926c
-- title:
--   Tate module determines the dimension of a p-divisible group
-- statement:
--   Fix a prime $p$, let $\mathbb{C}\mathrm{l} =$ `PadicAlgCl p` be the fixed algebraic closure of $\mathbb{Q}_p$ used throughout, and let $K$ be an intermediate field of $\mathbb{Q}_p \subseteq$ `PadicAlgCl p` that is finite-dimensional over $\mathbb{Q}_p$; write $\mathcal{O} =$ [`PadicAlgCl.ringOfIntegers p K`](def/PadicAlgCl_RingOfIntegers.html#L11) for the intersection of the integral closure of $\mathbb{Z}_p$ in `PadicAlgCl p` with $K$, viewed as a $\mathbb{Z}_p$-subalgebra. Let $h$ be a natural number and let $G$ and $\Gamma$ be two $p$-divisible groups over $\mathcal{O}$ of height $h$ in the sense of the structure [`PDivisibleGroup`](def/PDivisibleGroup_Basic.html#L199): towers of commutative cocommutative Hopf $\mathcal{O}$-algebras `level v`, finite and free of rank $p^{vh}$ over $\mathcal{O}$, with surjective coalgebra–algebra transition maps `level (v+1) → level v` whose kernels are the ideals obtained by transporting the augmentation ideal along multiplication by $p^{v}$. Let $n, n'$ be natural numbers and assume `G.HasDimension n` and `Γ.HasDimension n'`, i.e. for every $v$ the cotangent module of the $v$-th augmentation ideal of $G$ (resp. $\Gamma$) is $\mathcal{O}$-linearly isomorphic to $(\mathcal{O}/p^{v}\mathcal{O})^{n}$ (resp. $(\mathcal{O}/p^{v}\mathcal{O})^{n'}$). Let $e$ be an isomorphism of $\mathbb{Z}_p$-modules from [`TateModule p (Γ.Points (PadicAlgCl p))`](def/EllipticCurve_TateModule.html#L15) to [`TateModule p (G.Points (PadicAlgCl p))`](def/EllipticCurve_TateModule.html#L15), where `Points` is the direct limit over $v$ of the groups of $\mathcal{O}$-algebra maps from `level v` to `PadicAlgCl p` under convolution, and the Tate module consists of the sequences $(x_v)$ with $p^{v}x_v = 0$ and $p\,x_{v+1} = x_v$. Assume $e$ is equivariant for the termwise action `tateModuleRep` of every $\mathcal{O}$-algebra automorphism $\tau$ of `PadicAlgCl p`. Then $n = n'$.
--
--   This is Tate's corollary that the Galois module $T(G)$ determines the dimension of a $p$-divisible group over the ring of integers of a finite extension of $\mathbb{Q}_p$, deduced from the Hodge–Tate decomposition of $\mathbb{C}_p \otimes T(G)$ together with the vanishing of the Galois invariants of $\mathbb{C}_p(\chi^{k})$ for $k \neq 0$; both ingredients are cited by the proof. It is used in turn by [`PDivisibleGroup.forall_bijective_of_bijective_linearMap_tateModule_of_ringOfIntegers`](thm.html#PDivisibleGroup.forall_bijective_of_bijective_linearMap_tateModule_of_ringOfIntegers).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PDivisibleGroup_eq_of_hasDimension_of_linearEquiv_tateModule_of_ringOfIntegers.lean

import Mathlib
import Definitions.Def_PadicComplex_GaloisAction
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_PDivisibleGroup_Dimension
import Definitions.Def_PadicAlgCl_RingOfIntegers

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem PDivisibleGroup.eq_of_hasDimension_of_linearEquiv_tateModule_of_ringOfIntegers
    (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    {h : ℕ} (G Γ : PDivisibleGroup (PadicAlgCl.ringOfIntegers p K) p h) {n n' : ℕ}
    (hn : G.HasDimension n) (hn' : Γ.HasDimension n')
    (e : TateModule p (Γ.Points (PadicAlgCl p)) ≃ₗ[ℤ_[p]] TateModule p (G.Points (PadicAlgCl p)))
    (he : ∀ (τ : PadicAlgCl p ≃ₐ[(PadicAlgCl.ringOfIntegers p K)] PadicAlgCl p) (x : TateModule p (Γ.Points (PadicAlgCl p))),
      e (Γ.tateModuleRep (PadicAlgCl p) τ x) = G.tateModuleRep (PadicAlgCl p) τ (e x)) :
    n = n' := by sorry
