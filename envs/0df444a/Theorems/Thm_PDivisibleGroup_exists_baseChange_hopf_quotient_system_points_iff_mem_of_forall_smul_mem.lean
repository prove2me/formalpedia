-- Prove2me | Theorems.Thm_PDivisibleGroup_exists_baseChange_hopf_quotient_system_points_iff_mem_of_forall_smul_mem
-- name    : PDivisibleGroup.exists_baseChange_hopf_quotient_system_points_iff_mem_of_forall_smul_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:58.387243+00:00
-- url     : https://prove2.me/theorems/31dd8257-e2b9-52a9-95ff-73b00156e851
-- title:
--   Galois-stable Tate submodules cut out Hopf quotient systems over K'
-- statement:
--   Let $p$ be a prime, let $K$ be an intermediate field of $\mathbb{Q}_p \subseteq \overline{\mathbb{Q}}_p$ (here `PadicAlgCl p`) that is finite-dimensional over $\mathbb{Q}_p$, and let $\mathcal{O} =$ [`PadicAlgCl.ringOfIntegers p K`](def/PadicAlgCl_RingOfIntegers.html#L11) be the intersection of the integral closure of $\mathbb{Z}_p$ in $\overline{\mathbb{Q}}_p$ with $K$. Let $G$ be a $p$-divisible group of height $h$ over $\mathcal{O}$, i.e. a system of finite free cocommutative Hopf $\mathcal{O}$-algebras `G.level v` of rank $p^{vh}$ together with surjective bialgebra maps `G.transition v` whose kernels are the $p^v$-torsion ideals. Let $M$ be a $\mathbb{Z}_p$-submodule of the Tate module of the point group $G(\overline{\mathbb{Q}}_p)$, that is of the group of sequences $x$ with $p^n x_n = 0$ and $p\,x_{n+1} = x_n$, assumed stable under the componentwise action of every $\mathcal{O}$-algebra automorphism $\tau$ of $\overline{\mathbb{Q}}_p$, and saturated in the sense that $r \cdot x \in M$ with $r \in \mathbb{Z}_p$, $r \neq 0$, forces $x \in M$. Let $K'$ be a field realised as a fraction field of $\mathcal{O}$, with a compatible embedding into $\overline{\mathbb{Q}}_p$. Then there exist commutative rings $C_v$ ($v \in \mathbb{N}$) carrying Hopf $K'$-algebra structures and bialgebra maps $\pi_v \colon K' \otimes_{\mathcal{O}} G.\mathrm{level}\, v \to C_v$ such that: each $\pi_v$ is surjective; for every $a$ in level $v+1$, $\pi_{v+1}(1 \otimes a) = 0$ implies $\pi_v(1 \otimes \mathrm{transition}_v\, a) = 0$; and for every $v$ and every $\overline{\mathbb{Q}}_p$-point $g$ of level $v$ (an $\mathcal{O}$-algebra map $G.\mathrm{level}\,v \to \overline{\mathbb{Q}}_p$, taken in the convolution group), there is a $K'$-algebra map $g'' \colon C_v \to \overline{\mathbb{Q}}_p$ with $g''(\pi_v(1 \otimes a)) = g(a)$ for all $a$ if and only if the image of $g$ in the direct limit $G(\overline{\mathbb{Q}}_p)$ is the $v$-th component of some element of $M$.
--
--   This is the generic-fibre half of the first step of Tate's proof that a Galois-stable saturated submodule of the Tate module comes from a $p$-divisible subgroup: the subgroups $M_v = \{x_v : x \in M\}$ of the étale groups $G_v(\overline{\mathbb{Q}}_p)$ are cut out by Hopf ideals already defined over the fraction field $K'$ of $\mathcal{O}$, Galois descent being available because $M$ is stable. It feeds the corresponding statement over the ring of integers, obtained by taking schematic closures.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PDivisibleGroup_exists_baseChange_hopf_quotient_system_points_iff_mem_of_forall_smul_mem.lean

import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_PadicAlgCl_RingOfIntegers

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
set_option Elab.async false

open scoped TensorProduct

theorem PDivisibleGroup.exists_baseChange_hopf_quotient_system_points_iff_mem_of_forall_smul_mem
    (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    {h : ℕ} (G : PDivisibleGroup (PadicAlgCl.ringOfIntegers p K) p h)
    (M : Submodule ℤ_[p] (TateModule p (G.Points (PadicAlgCl p))))
    (hMstab : ∀ (τ : PadicAlgCl p ≃ₐ[PadicAlgCl.ringOfIntegers p K] PadicAlgCl p)
        (x : TateModule p (G.Points (PadicAlgCl p))),
      x ∈ M → G.tateModuleRep (PadicAlgCl p) τ x ∈ M)
    (hMsat : ∀ (r : ℤ_[p]) (x : TateModule p (G.Points (PadicAlgCl p))), r ≠ 0 → r • x ∈ M → x ∈ M)
    (K' : Type) [Field K'] [Algebra (PadicAlgCl.ringOfIntegers p K) K'] [IsFractionRing (PadicAlgCl.ringOfIntegers p K) K']
    [Algebra K' (PadicAlgCl p)] [IsScalarTower (PadicAlgCl.ringOfIntegers p K) K' (PadicAlgCl p)] :
    ∃ (C : ℕ → Type) (_ : ∀ v, CommRing (C v)) (_ : ∀ v, HopfAlgebra K' (C v))
      (πK : ∀ v, K' ⊗[PadicAlgCl.ringOfIntegers p K] G.level v →ₐc[K'] C v),
      (∀ v, Function.Surjective (πK v)) ∧
      (∀ (v : ℕ) (a : G.level (v + 1)),
        πK (v + 1) ((1 : K') ⊗ₜ[PadicAlgCl.ringOfIntegers p K] a) = 0 →
          πK v ((1 : K') ⊗ₜ[PadicAlgCl.ringOfIntegers p K] G.transition v a) = 0) ∧
      (∀ (v : ℕ) (g : G.Point (PadicAlgCl p) v),
        (∃ g'' : C v →ₐ[K'] PadicAlgCl p, ∀ a : G.level v,
            g'' (πK v ((1 : K') ⊗ₜ[PadicAlgCl.ringOfIntegers p K] a)) = PDivisibleGroup.Point.toAlgHom g a) ↔
          ∃ x ∈ M, G.pointsMkAdd (PadicAlgCl p) v (Additive.ofMul g) =
            (x : ℕ → G.Points (PadicAlgCl p)) v) := by sorry
