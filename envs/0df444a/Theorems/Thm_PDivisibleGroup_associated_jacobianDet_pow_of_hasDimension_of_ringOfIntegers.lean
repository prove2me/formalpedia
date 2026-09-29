-- Prove2me | Theorems.Thm_PDivisibleGroup_associated_jacobianDet_pow_of_hasDimension_of_ringOfIntegers
-- name    : PDivisibleGroup.associated_jacobianDet_pow_of_hasDimension_of_ringOfIntegers
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:58.387243+00:00
-- url     : https://prove2.me/theorems/e48549ac-72d2-5af1-a268-a99c65340e3b
-- title:
--   Jacobian determinant of a square presentation of Gᵥ
-- statement:
--   Let $p$ be a prime and let $K$ be an intermediate field of $\mathbb{Q}_p$ inside `PadicAlgCl p` which is finite-dimensional over $\mathbb{Q}_p$; write $\mathcal{O} =$ [`PadicAlgCl.ringOfIntegers p K`](def/PadicAlgCl_RingOfIntegers.html#L11), the $\mathbb{Z}_p$-subalgebra of `PadicAlgCl p` obtained as the intersection of the integral closure of $\mathbb{Z}_p$ in `PadicAlgCl p` with $K$. Let $G$ be a $p$-divisible group over $\mathcal{O}$ of height $h$ in the sense of the structure [`PDivisibleGroup`](def/PDivisibleGroup_Basic.html#L199): a family of commutative rings `G.level v` carrying cocommutative Hopf algebra structures over $\mathcal{O}$ and finite free as $\mathcal{O}$-modules, with surjective coalgebra transition maps `G.level (v+1) → G.level v`, with $\operatorname{rank}_{\mathcal{O}}$ `G.level v` $= p^{vh}$, and with the kernel of the $v$-th transition map equal to the torsion ideal [`PDivisibleGroup.Hopf.torsionIdeal`](def/PDivisibleGroup_Basic.html#L157) of `G.level (v+1)` at $p^v$ (the image of the augmentation ideal under multiplication by $p^v$). Assume `G.HasDimension n`, i.e. for every $w$ the cotangent module $I/I^2$ of the ideal `G.augIdeal w` of `G.level w` is isomorphic, as an $\mathcal{O}$-module, to $(\mathcal{O}/p^w\mathcal{O})^n$. Fix $v$, and suppose given $m$ polynomials $f_0,\dots,f_{m-1} \in \mathcal{O}[X_0,\dots,X_{m-1}]$ in the same number $m$ of variables together with an $\mathcal{O}$-algebra isomorphism $e$ from $\mathcal{O}[X_0,\dots,X_{m-1}]/(f_0,\dots,f_{m-1})$ onto `G.level v`. Then the image under $e$ of the class of the determinant of the $m \times m$ matrix $(\partial f_i/\partial X_j)_{i,j}$ is associated, in the ring `G.level v`, to $p^{nv}$; that is, the two differ by a unit of `G.level v`.
--
--   This is Tate's computation of the Jacobian of a square presentation of the $v$-th level of a $p$-divisible group of dimension $n$ over the ring of integers of a finite extension of $\mathbb{Q}_p$: the Jacobian ideal is the Fitting ideal of the module of invariant differentials, which by the dimension hypothesis is $(\mathcal{O}/p^v)^n$. It is used to evaluate the discriminant of `G.level v` in [`PDivisibleGroup.associated_discr_level_of_hasDimension_of_ringOfIntegers`](thm.html#PDivisibleGroup.associated_discr_level_of_hasDimension_of_ringOfIntegers).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PDivisibleGroup_associated_jacobianDet_pow_of_hasDimension_of_ringOfIntegers.lean

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

theorem PDivisibleGroup.associated_jacobianDet_pow_of_hasDimension_of_ringOfIntegers
    (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    {h : ℕ} (G : PDivisibleGroup (PadicAlgCl.ringOfIntegers p K) p h) {n : ℕ} (hn : G.HasDimension n) (v : ℕ)
    {m : ℕ} (f : Fin m → MvPolynomial (Fin m) (PadicAlgCl.ringOfIntegers p K))
    (e : (MvPolynomial (Fin m) (PadicAlgCl.ringOfIntegers p K) ⧸ Ideal.span (Set.range f)) ≃ₐ[PadicAlgCl.ringOfIntegers p K]
      G.level v) :
    Associated (e (Ideal.Quotient.mk _ (Matrix.det (Matrix.of fun i j => MvPolynomial.pderiv j (f i)))))
      (((p : ℕ) : G.level v) ^ (n * v)) := by sorry
