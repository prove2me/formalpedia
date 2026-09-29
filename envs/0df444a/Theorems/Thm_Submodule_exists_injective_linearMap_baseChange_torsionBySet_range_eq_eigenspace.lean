-- Prove2me | Theorems.Thm_Submodule_exists_injective_linearMap_baseChange_torsionBySet_range_eq_eigenspace
-- name    : Submodule.exists_injective_linearMap_baseChange_torsionBySet_range_eq_eigenspace
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.134728+00:00
-- url     : https://prove2.me/theorems/411d330d-ff01-5f25-8677-b20c7bb1886f
-- title:
--   Base change k⊗_{A/𝔪}J[𝔪] as ι-eigenspace in k⊗_ℤJ[I]
-- statement:
--   Let $A$ be a commutative ring, $J$ an $A$-module, $k$ a field of characteristic $p$ for a prime number $p$, and let $I$ and $\mathfrak m$ be ideals of $A$ with $\mathfrak m$ maximal, $I \subseteq \mathfrak m$, and $p$ (the image of the natural number $p$ in $A$) lying in $I$. Write $J[I] = \{x \in J : a x = 0 \text{ for all } a \in I\}$ and $J[\mathfrak m] = \{x \in J : a x = 0 \text{ for all } a \in \mathfrak m\}$ for the torsion submodules cut out by the underlying sets of $I$ and $\mathfrak m$, and assume $J[I]$ is finite. Let $\iota : A/\mathfrak m \to k$ be a ring homomorphism, and regard $k$ as an $A/\mathfrak m$-algebra through $\iota$, so that $k \otimes_{A/\mathfrak m} J[\mathfrak m]$ makes sense for the natural $A/\mathfrak m$-module structure on $J[\mathfrak m]$. Then there exists a $k$-linear map $j : k \otimes_{A/\mathfrak m} J[\mathfrak m] \to k \otimes_{\mathbb Z} J[I]$ which is injective and whose range consists exactly of those $w \in k \otimes_{\mathbb Z} J[I]$ such that, for every $a \in A$, the base change to $k$ of the $\mathbb Z$-linear endomorphism $x \mapsto a x$ of $J[I]$ sends $w$ to $\iota(a \bmod \mathfrak m) \cdot w$.
--
--   This identifies the $k$-valued eigenspace for the character $\iota$ of the $A$-action on the finite $p$-torsion group $J[I]$, after base change to $k$, with the $\iota$-twisted base change of the residual torsion module $J[\mathfrak m]$; note that the map $j$ is not the naive assignment $c \otimes x \mapsto c \otimes x$, which is not $A/\mathfrak m$-balanced. It is used in the construction of the cohomological carrier, in [`CohCarrier.exists_ideal_H1_top_to_dual_baseChange_heckeTorsion_jZero_of_isAbsolutelyIrreducible`](thm.html#CohCarrier.exists_ideal_H1_top_to_dual_baseChange_heckeTorsion_jZero_of_isAbsolutelyIrreducible), to pass between Hecke torsion modules and eigenspaces over a coefficient field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Submodule_exists_injective_linearMap_baseChange_torsionBySet_range_eq_eigenspace.lean

import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Algebra.CharP.Defs
import Mathlib.RingTheory.Ideal.Quotient.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct in

theorem Submodule.exists_injective_linearMap_baseChange_torsionBySet_range_eq_eigenspace
    {A : Type*} [CommRing A] {J : Type*} [AddCommGroup J] [Module A J]
    {k : Type*} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (I 𝔪 : Ideal A) [𝔪.IsMaximal] (hI : I ≤ 𝔪) (hp : (p : A) ∈ I)
    (hfin : Finite ↥(Submodule.torsionBySet A J (I : Set A)))
    (ι : A ⧸ 𝔪 →+* k) :
    letI := ι.toAlgebra
    ∃ j : k ⊗[A ⧸ 𝔪] ↥(Submodule.torsionBySet A J (𝔪 : Set A)) →ₗ[k]
        k ⊗[ℤ] ↥(Submodule.torsionBySet A J (I : Set A)),
      Function.Injective j ∧
      ∀ w : k ⊗[ℤ] ↥(Submodule.torsionBySet A J (I : Set A)),
        w ∈ LinearMap.range j ↔
          ∀ a : A,
            ((DistribSMul.toLinearMap ℤ ↥(Submodule.torsionBySet A J (I : Set A)) a).baseChange k) w =
              ι (Ideal.Quotient.mk 𝔪 a) • w := by sorry
