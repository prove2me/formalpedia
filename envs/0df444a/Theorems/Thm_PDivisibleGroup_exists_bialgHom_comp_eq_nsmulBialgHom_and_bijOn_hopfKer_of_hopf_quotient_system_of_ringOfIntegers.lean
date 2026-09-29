-- Prove2me | Theorems.Thm_PDivisibleGroup_exists_bialgHom_comp_eq_nsmulBialgHom_and_bijOn_hopfKer_of_hopf_quotient_system_of_ringOfIntegers
-- name    : PDivisibleGroup.exists_bialgHom_comp_eq_nsmulBialgHom_and_bijOn_hopfKer_of_hopf_quotient_system_of_ringOfIntegers
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:58.387243+00:00
-- url     : https://prove2.me/theorems/c537778a-c163-5be0-977a-34a77182fb60
-- title:
--   Multiplication by p along a Hopf quotient tower stabilises
-- statement:
--   Fix a prime $p$ and an intermediate field $K$ of $\overline{\mathbb Q}_p/\mathbb Q_p$ that is finite over $\mathbb Q_p$, and write $\mathcal O$ for [`PadicAlgCl.ringOfIntegers p K`](def/PadicAlgCl_RingOfIntegers.html#L11), the intersection of the integral closure of $\mathbb Z_p$ in $\overline{\mathbb Q}_p$ with $K$. Let $G$ be a $p$-divisible group of height $h$ over $\mathcal O$, i.e. a system of cocommutative Hopf algebras $G.level\,v$ that are finite free $\mathcal O$-modules of rank $p^{vh}$, with surjective bialgebra transitions $G.level(v+1)\to G.level\,v$ whose ring-theoretic kernels are the $p^v$-torsion ideals. Let $M$ be a $\mathbb Z_p$-submodule of the Tate module $T(G)$, the group of sequences $x:\mathbb N\to G.Points(\overline{\mathbb Q}_p)$ with $p^n x_n=0$ and $p\,x_{n+1}=x_n$, assumed stable under the coordinatewise action of the $\mathcal O$-algebra automorphisms of $\overline{\mathbb Q}_p$ and saturated, in the sense that $r\neq 0$ and $rx\in M$ imply $x\in M$. Let $B:\mathbb N\to\mathrm{Type}$ be a family of cocommutative Hopf $\mathcal O$-algebras, each finite and free as an $\mathcal O$-module, equipped with surjective bialgebra maps $\pi_v:G.level\,v\to B_v$ and $t_v:B_{v+1}\to B_v$ such that $G.transition_v$ followed by $\pi_v$ equals $\pi_{v+1}$ followed by $t_v$, and such that for every $v$ and every point $g$ of $G$ of level $v$ with values in $\overline{\mathbb Q}_p$ (an $\mathcal O$-algebra map $G.level\,v\to\overline{\mathbb Q}_p$, taken in the convolution group), the map $g$ factors through $\pi_v$ by some $\mathcal O$-algebra map $B_v\to\overline{\mathbb Q}_p$ if and only if the image of $g$ in $G.Points(\overline{\mathbb Q}_p)$ under the canonical map from level $v$ is the $v$-th coordinate of some $x\in M$. The conclusion asserts the existence of bialgebra maps $m_j:B_j\to B_{j+1}$ over $\mathcal O$ such that: $t_j$ followed by $m_j$ is the $p$-fold convolution power `nsmulBialgHom` of the identity on $B_{j+1}$; $m_j$ followed by $t_j$ is the corresponding map on $B_j$; for every $j$ and every $d$ in [`HopfAlgebra.hopfKer (t j)`](def/HopfAlgebra_HopfKer.html#L19), the subalgebra of $B_{j+1}$ on which the $t_j$-coaction agrees with $a\mapsto a\otimes 1$, the $p$-fold convolution power of the identity algebra endomorphism of $B_{j+1}$ sends $d$ to the image of its counit under the structure map $\mathcal O\to B_{j+1}$; $m_{j+1}$ maps `hopfKer (t j)` into `hopfKer (t (j+1))`; and there is an index $i_0$ such that for all $i\ge i_0$ the map $m_{i+1}$ restricts to a bijection from `hopfKer (t i)` onto `hopfKer (t (i+1))`.
--
--   This is the subquotient-tower step in Tate's proof that a saturated Galois-stable submodule of the Tate module is cut out by a $p$-divisible subgroup: multiplication by $p$ on $E_{j+1}=\operatorname{Spec}B_{j+1}$ factors through $E_j$, each subquotient $E_{j+1}/E_j$ is killed by $p$, and the increasing chain of affine algebras of the subquotients stabilises from some index $i_0$ on. It is used to construct the $p$-divisible group attached to the closure system, in [`PDivisibleGroup.exists_pDivisibleGroup_bialgHom_linearMap_tateModule_injective_range_eq_of_hopf_quotient_system_of_ringOfIntegers`](thm.html#PDivisibleGroup.exists_pDivisibleGroup_bialgHom_linearMap_tateModule_injective_range_eq_of_hopf_quotient_system_of_ringOfIntegers).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PDivisibleGroup_exists_bialgHom_comp_eq_nsmulBialgHom_and_bijOn_hopfKer_of_hopf_quotient_system_of_ringOfIntegers.lean

import Mathlib
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_PDivisibleGroup_Tower
import Definitions.Def_PadicAlgCl_RingOfIntegers
import Definitions.Def_HopfAlgebra_HopfKer

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem PDivisibleGroup.exists_bialgHom_comp_eq_nsmulBialgHom_and_bijOn_hopfKer_of_hopf_quotient_system_of_ringOfIntegers
    (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    {h : ℕ} (G : PDivisibleGroup (PadicAlgCl.ringOfIntegers p K) p h)
    (M : Submodule ℤ_[p] (TateModule p (G.Points (PadicAlgCl p))))
    (hMstab : ∀ (τ : PadicAlgCl p ≃ₐ[PadicAlgCl.ringOfIntegers p K] PadicAlgCl p)
        (x : TateModule p (G.Points (PadicAlgCl p))),
      x ∈ M → G.tateModuleRep (PadicAlgCl p) τ x ∈ M)
    (hMsat : ∀ (r : ℤ_[p]) (x : TateModule p (G.Points (PadicAlgCl p))), r ≠ 0 → r • x ∈ M → x ∈ M)
    (B : ℕ → Type) [∀ v, CommRing (B v)] [∀ v, HopfAlgebra (PadicAlgCl.ringOfIntegers p K) (B v)]
    [∀ v, Coalgebra.IsCocomm (PadicAlgCl.ringOfIntegers p K) (B v)]
    [∀ v, Module.Finite (PadicAlgCl.ringOfIntegers p K) (B v)]
    [∀ v, Module.Free (PadicAlgCl.ringOfIntegers p K) (B v)]
    (π : ∀ v, G.level v →ₐc[PadicAlgCl.ringOfIntegers p K] B v)
    (t : ∀ v, B (v + 1) →ₐc[PadicAlgCl.ringOfIntegers p K] B v)
    (hπ : ∀ v, Function.Surjective (π v)) (ht : ∀ v, Function.Surjective (t v))
    (hπt : ∀ v, (π v).comp (G.transition v) = (t v).comp (π (v + 1)))
    (hpts : ∀ (v : ℕ) (g : G.Point (PadicAlgCl p) v),
        (∃ g' : B v →ₐ[PadicAlgCl.ringOfIntegers p K] PadicAlgCl p,
            g'.comp (π v : G.level v →ₐ[PadicAlgCl.ringOfIntegers p K] B v) =
              PDivisibleGroup.Point.toAlgHom g) ↔
          ∃ x ∈ M, G.pointsMkAdd (PadicAlgCl p) v (Additive.ofMul g) =
            (x : ℕ → G.Points (PadicAlgCl p)) v) :
    ∃ m : ∀ j, B j →ₐc[PadicAlgCl.ringOfIntegers p K] B (j + 1),
      (∀ j, (m j).comp (t j) = PDivisibleGroup.Hopf.nsmulBialgHom (PadicAlgCl.ringOfIntegers p K) (B (j + 1)) p) ∧
      (∀ j, (t j).comp (m j) = PDivisibleGroup.Hopf.nsmulBialgHom (PadicAlgCl.ringOfIntegers p K) (B j) p) ∧
      (∀ j, ∀ d ∈ HopfAlgebra.hopfKer (t j),
        PDivisibleGroup.Hopf.nsmulAlgHom (PadicAlgCl.ringOfIntegers p K) (B (j + 1)) p d =
          algebraMap (PadicAlgCl.ringOfIntegers p K) (B (j + 1)) (Coalgebra.counit d)) ∧
      (∀ j, Set.MapsTo (m (j + 1)) (HopfAlgebra.hopfKer (t j) : Set (B (j + 1)))
        (HopfAlgebra.hopfKer (t (j + 1)) : Set (B (j + 2)))) ∧
      ∃ i₀ : ℕ, ∀ i, i₀ ≤ i →
        Set.BijOn (m (i + 1)) (HopfAlgebra.hopfKer (t i) : Set (B (i + 1)))
          (HopfAlgebra.hopfKer (t (i + 1)) : Set (B (i + 2))) := by sorry
