-- Prove2me | Theorems.Thm_ProjSpaceCech_GradedModule_subsingleton_cohomology_shift_of_isFG
-- name    : ProjSpaceCech.GradedModule.subsingleton_cohomology_shift_of_isFG
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.214879+00:00
-- url     : https://prove2.me/theorems/03df9cb4-5f08-5669-b60c-170be5da3870
-- title:
--   Serre vanishing for finitely generated graded modules
-- statement:
--   Let $R$ be a commutative Noetherian ring, let $n \in \mathbb{N}$, and let $M$ be an object of [`ProjSpaceCech.GradedModule R n`](def/AlgebraicGeometry_ProjSpaceCechGradedModule.html#L18): an $R$-module $M$ together with a family of $R$-submodules $M_d \subseteq M$ indexed by $d \in \mathbb{Z}$ (`grade`) and $R$-linear endomorphisms $x_j \cdot$ for $j \in \{0,\dots,n\}$ (`xMul`) that carry $M_d$ into $M_{d+1}$ and commute with one another. Assume `IsFG M`, that is, that there exists a presentation of $M$ in the sense of `GradedModule.Presentation`: a finite index type $J$, integers $d_0(k)$ for $k \in J$, and a morphism of graded modules from $\prod_{k \in J} \mathrm{FD}\,R\,n\,(d_0(k))$ to $M$ whose underlying linear map hits, for every $d$, every element of $M_d$ by an element of degree $d$ of the source. Then there is $d_0 \in \mathbb{Z}$ such that for every $d \ge d_0$ and every $i \ge 1$ the type `GradedModule.H (GradedModule.shift M d) i` is a subsingleton, where `shift M d` is $M$ with grading re-indexed by $(\text{shift } M\, d)_e = M_{e+d}$, and where `H D i` is the $i$-th cohomology of the alternating Čech complex of $D$, namely $\ker d^0$ for $i = 0$ and $\ker d^{i+1}$ modulo the preimage of the image of $d^{i}$ for $i+1 \ge 1$.
--
--   This is the purely graded-algebraic form of Serre's vanishing theorem: for a finitely generated graded module over $R[x_0,\dots,x_n]$ with $R$ Noetherian, the higher Čech cohomology of the associated sheaf on $\mathbb{P}^n_R$ vanishes after a sufficiently positive twist. It feeds the computation of the degree-zero cohomology of shifts of such a module and, through [`AlgebraicGeometry.ProjSpace.exists_forall_subsingleton_HSucc_twist`](thm.html#AlgebraicGeometry.ProjSpace.exists_forall_subsingleton_HSucc_twist), the scheme-theoretic statement for twists of coherent sheaves on projective space.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ProjSpaceCech_GradedModule_subsingleton_cohomology_shift_of_isFG.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpaceCechTwist
import Definitions.Def_AlgebraicGeometry_ProjSpaceCechGradedModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem ProjSpaceCech.GradedModule.subsingleton_cohomology_shift_of_isFG {R : Type u} [CommRing R] [IsNoetherianRing R] {n : ℕ}
    (M : ProjSpaceCech.GradedModule R n) (hM : ProjSpaceCech.GradedModule.IsFG M) :
    ∃ d₀ : ℤ, ∀ d, d₀ ≤ d → ∀ i, 1 ≤ i → Subsingleton (ProjSpaceCech.GradedModule.H (ProjSpaceCech.GradedModule.shift M d) i) := by sorry
