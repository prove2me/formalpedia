-- Prove2me | Theorems.Thm_PDivisibleGroup_exists_pDivisibleGroup_bialgHom_linearMap_tateModule_ker_eq_of_forall_smul_mem_of_ringOfIntegers
-- name    : PDivisibleGroup.exists_pDivisibleGroup_bialgHom_linearMap_tateModule_ker_eq_of_forall_smul_mem_of_ringOfIntegers
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:58.387243+00:00
-- url     : https://prove2.me/theorems/3d4e9f54-07d4-5676-8440-1249c0bfbdef
-- title:
--   Tate's Proposition 12, quotient form, over mathcal O_K
-- statement:
--   Fix a prime $p$ and an intermediate field $K$ of $\mathbb{Q}_p \subseteq \overline{\mathbb{Q}}_p$ (the latter realised as `PadicAlgCl p`) with $K/\mathbb{Q}_p$ finite, and put $\mathcal O =$ [`PadicAlgCl.ringOfIntegers p K`](def/PadicAlgCl_RingOfIntegers.html#L11), the intersection of the integral closure of $\mathbb Z_p$ in $\overline{\mathbb Q}_p$ with $K$, viewed as a $\mathbb Z_p$-subalgebra. Let $G$ be a [`PDivisibleGroup`](def/PDivisibleGroup_Basic.html#L199) over $\mathcal O$ of parameters $p, h$: a system of finite free cocommutative Hopf $\mathcal O$-algebras `G.level v` of rank $p^{vh}$, with surjective bialgebra transition maps whose kernels are the $p^v$-torsion ideals. Write $T(G) =$ [`TateModule p (G.Points (PadicAlgCl p))`](def/EllipticCurve_TateModule.html#L15) for the group of sequences $(x_n)$ of points of $G$ over $\overline{\mathbb Q}_p$ (elements of the direct limit of the groups `G.Point (PadicAlgCl p) v`) satisfying $p^n x_n = 0$ and $p\,x_{n+1} = x_n$, a $\mathbb Z_p$-module on which the $\mathcal O$-algebra automorphisms $\tau$ of $\overline{\mathbb Q}_p$ act componentwise via `G.tateModuleRep`. Let $M \subseteq T(G)$ be a $\mathbb Z_p$-submodule that is stable under all these $\tau$ and saturated ($r \neq 0$ and $r \cdot x \in M$ imply $x \in M$). The assertion is that there exist $h'$, a [`PDivisibleGroup`](def/PDivisibleGroup_Basic.html#L199) $Q$ over $\mathcal O$ with parameters $p, h'$, bialgebra maps $\psi_v : Q.\mathrm{level}\,v \to G.\mathrm{level}\,v$ over $\mathcal O$ and a $\mathbb Z_p$-linear map $T\psi : T(G) \to T(Q)$ such that: $\psi_v$ followed by nothing, precisely $\psi_v \circ (Q.\mathrm{transition}\,v) = (G.\mathrm{transition}\,v) \circ \psi_{v+1}$ for all $v$; $T\psi$ is computed levelwise, in that whenever the $n$-th component of $x$ is the class of a point $g$ at level $w$, the $n$-th component of $T\psi(x)$ is the class at level $w$ of the point whose algebra map is $\psi_w$ followed by the algebra map of $g$; $T\psi$ commutes with the actions of every $\tau$; $\ker T\psi = M$; and every $z \in T(Q)$ admits $k \in \mathbb N$ and $y \in T(G)$ with $p^k z = T\psi(y)$. The last clause is weaker than what the argument produces, namely that $T\psi$ is surjective (the case $k = 0$).
--
--   This is the quotient (image) form of Tate's Proposition 12 in §4.2 of "p-divisible groups": a Galois-stable saturated submodule of the Tate module of a $p$-divisible group over the ring of integers of a finite extension of $\mathbb Q_p$ is the kernel of the Tate-module map attached to a homomorphism onto a $p$-divisible group. It is used in the study of the action of inertia on Tate modules, via the statement [`PDivisibleGroup.forall_dual_apply_eq_zero_of_forall_norm_sub_counit_lt_one_of_forall_inertia_of_ringOfIntegers`](thm.html#PDivisibleGroup.forall_dual_apply_eq_zero_of_forall_norm_sub_counit_lt_one_of_forall_inertia_of_ringOfIntegers).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PDivisibleGroup_exists_pDivisibleGroup_bialgHom_linearMap_tateModule_ker_eq_of_forall_smul_mem_of_ringOfIntegers.lean

import Mathlib
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_PadicAlgCl_RingOfIntegers
import Definitions.Def_GaloisRep_CompletionBridge

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem PDivisibleGroup.exists_pDivisibleGroup_bialgHom_linearMap_tateModule_ker_eq_of_forall_smul_mem_of_ringOfIntegers
    (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    {h : ℕ} (G : PDivisibleGroup (PadicAlgCl.ringOfIntegers p K) p h)
    (M : Submodule ℤ_[p] (TateModule p (G.Points (PadicAlgCl p))))
    (hMstab : ∀ (τ : PadicAlgCl p ≃ₐ[PadicAlgCl.ringOfIntegers p K] PadicAlgCl p) (x : TateModule p (G.Points (PadicAlgCl p))),
      x ∈ M → G.tateModuleRep (PadicAlgCl p) τ x ∈ M)
    (hMsat : ∀ (r : ℤ_[p]) (x : TateModule p (G.Points (PadicAlgCl p))), r ≠ 0 → r • x ∈ M → x ∈ M) :
    ∃ (h' : ℕ) (Q : PDivisibleGroup (PadicAlgCl.ringOfIntegers p K) p h')
      (ψ : ∀ v : ℕ, Q.level v →ₐc[PadicAlgCl.ringOfIntegers p K] G.level v)
      (Tψ : TateModule p (G.Points (PadicAlgCl p)) →ₗ[ℤ_[p]] TateModule p (Q.Points (PadicAlgCl p))),
      (∀ v : ℕ, (ψ v).comp (Q.transition v) = (G.transition v).comp (ψ (v + 1))) ∧
      (∀ (x : TateModule p (G.Points (PadicAlgCl p))) (n w : ℕ) (g : G.Point (PadicAlgCl p) w),
        G.pointsMkAdd (PadicAlgCl p) w (Additive.ofMul g) = (x : ℕ → G.Points (PadicAlgCl p)) n →
        ((Tψ x : TateModule p (Q.Points (PadicAlgCl p))) : ℕ → Q.Points (PadicAlgCl p)) n =
          Q.pointsMkAdd (PadicAlgCl p) w (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
            ((PDivisibleGroup.Point.toAlgHom g).comp (ψ w : Q.level w →ₐ[PadicAlgCl.ringOfIntegers p K] G.level w))))) ∧
      (∀ (τ : PadicAlgCl p ≃ₐ[PadicAlgCl.ringOfIntegers p K] PadicAlgCl p) (x : TateModule p (G.Points (PadicAlgCl p))),
        Tψ (G.tateModuleRep (PadicAlgCl p) τ x) = Q.tateModuleRep (PadicAlgCl p) τ (Tψ x)) ∧
      LinearMap.ker Tψ = M ∧
      (∀ z : TateModule p (Q.Points (PadicAlgCl p)), ∃ (k : ℕ) (y : TateModule p (G.Points (PadicAlgCl p))),
        ((p : ℤ_[p]) ^ k) • z = Tψ y) := by sorry
