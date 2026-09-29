-- Prove2me | Theorems.Thm_PDivisibleGroup_exists_bialgHom_comp_transition_eq_and_injective_of_hopf_quotient_system_of_tower_of_ringOfIntegers
-- name    : PDivisibleGroup.exists_bialgHom_comp_transition_eq_and_injective_of_hopf_quotient_system_of_tower_of_ringOfIntegers
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:58.387243+00:00
-- url     : https://prove2.me/theorems/4f800797-d02a-524b-a244-493316a9ad0c
-- title:
--   Tate's Proposition 12: maps onto the subquotient tower
-- statement:
--   Let $p$ be a prime, $K$ a finite extension of $\mathbb{Q}_p$ inside a fixed algebraic closure $\overline{\mathbb{Q}}_p =$ `PadicAlgCl p`, and $\mathcal{O} =$ [`PadicAlgCl.ringOfIntegers p K`](def/PadicAlgCl_RingOfIntegers.html#L11), the intersection of the integral closure of $\mathbb{Z}_p$ in $\overline{\mathbb{Q}}_p$ with $K$. Let $G$ be a $p$-divisible group of height $h$ over $\mathcal{O}$, that is, a family of cocommutative Hopf $\mathcal{O}$-algebras `G.level v` that are finite free as $\mathcal{O}$-modules, of rank $p^{vh}$, with surjective transition bialgebra maps $\mathrm{tr}_v \colon$ `G.level (v+1)` $\to$ `G.level v` whose kernels are the $p^v$-torsion ideals. Let $M$ be a $\mathbb{Z}_p$-submodule of the Tate module $T(G) = \{x \colon \mathbb{N} \to G(\overline{\mathbb{Q}}_p) : p^n x_n = 0,\ p\,x_{n+1} = x_n\}$ (points being taken in the direct limit of the groups of $\mathcal{O}$-algebra maps `G.level v` $\to \overline{\mathbb{Q}}_p$ under convolution), assumed stable under the action of all $\mathcal{O}$-algebra automorphisms of $\overline{\mathbb{Q}}_p$ through `G.tateModuleRep` and saturated ($r \neq 0$ and $rx \in M$ imply $x \in M$). Assume given: a tower $B$ of cocommutative Hopf $\mathcal{O}$-algebras, finite and free over $\mathcal{O}$, with surjections $\pi_v \colon$ `G.level v` $\twoheadrightarrow B_v$ and $t_v \colon B_{v+1} \twoheadrightarrow B_v$ of bialgebras satisfying $\pi_v \circ \mathrm{tr}_v = t_v \circ \pi_{v+1}$, such that for every $v$ an $\overline{\mathbb{Q}}_p$-point $g$ of `G.level v` factors through $\pi_v$ exactly when its image in $G(\overline{\mathbb{Q}}_p)$ is the $v$-th component of some $x \in M$; bialgebra maps $m_j \colon B_j \to B_{j+1}$ with $m_j \circ t_j$ and $t_j \circ m_j$ both equal to the $p$-th convolution power of the identity (multiplication by $p$) on $B_{j+1}$, respectively $B_j$; an index $i_0$; and a further tower $L$ of cocommutative Hopf $\mathcal{O}$-algebras, finite free over $\mathcal{O}$, with bialgebra maps $t'_v \colon L_{v+1} \to L_v$ and injective bialgebra maps $\iota_v \colon L_v \to B_{i_0+v}$ whose images are exactly the Hopf kernel (the equaliser of the coaction with `includeLeft`) of the composite transition map [`PDivisibleGroup.Tower.transitionLE t i₀ v`](def/PDivisibleGroup_Tower.html#L198) $\colon B_{i_0+v} \to B_{i_0}$, and with $\iota_v \circ t'_v = t_{i_0+v} \circ \iota_{v+1}$. Then there is a family of bialgebra maps $\varphi_v \colon$ `G.level v` $\to L_v$ such that $\varphi_v \circ \mathrm{tr}_v = t'_v \circ \varphi_{v+1}$ for all $v$; precomposition with $\varphi_v$ is injective on $\mathcal{O}$-algebra maps $L_v \to \overline{\mathbb{Q}}_p$; and an $\mathcal{O}$-algebra map $y \colon$ `G.level v` $\to \overline{\mathbb{Q}}_p$ factors as $\gamma \circ \varphi_v$ for some $\gamma \colon L_v \to \overline{\mathbb{Q}}_p$ precisely when the corresponding point of $G(\overline{\mathbb{Q}}_p)$ is the $v$-th component of some element of $M$.
--
--   This is the Hopf-algebra form of the construction in Tate's Proposition 12: on schemes the maps $\varphi_v$ are induced by multiplication by $p^{i_0}$ from the closure system $E_{i_0+v}$ to $E_v$, which kills $E_{i_0}$ and hence factors through the quotient tower $\Gamma_v = E_{i_0+v}/E_{i_0}$ whose coordinate rings are the $L_v$. It is used in the proof that a Galois-stable saturated submodule of the Tate module of a $p$-divisible group over the ring of integers is the Tate module of a $p$-divisible subgroup.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PDivisibleGroup_exists_bialgHom_comp_transition_eq_and_injective_of_hopf_quotient_system_of_tower_of_ringOfIntegers.lean

import Mathlib
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_PadicAlgCl_RingOfIntegers
import Definitions.Def_PDivisibleGroup_Tower
import Definitions.Def_HopfAlgebra_HopfKer

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem PDivisibleGroup.exists_bialgHom_comp_transition_eq_and_injective_of_hopf_quotient_system_of_tower_of_ringOfIntegers
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
            (x : ℕ → G.Points (PadicAlgCl p)) v)
    (m : ∀ j, B j →ₐc[(PadicAlgCl.ringOfIntegers p K)] B (j + 1))
    (hmt : ∀ j, (m j).comp (t j) = PDivisibleGroup.Hopf.nsmulBialgHom (PadicAlgCl.ringOfIntegers p K) (B (j + 1)) p)
    (htm : ∀ j, (t j).comp (m j) = PDivisibleGroup.Hopf.nsmulBialgHom (PadicAlgCl.ringOfIntegers p K) (B j) p)
    (i₀ : ℕ)
    (L : ℕ → Type) [∀ v, CommRing (L v)] [∀ v, HopfAlgebra (PadicAlgCl.ringOfIntegers p K) (L v)]
    [∀ v, Coalgebra.IsCocomm (PadicAlgCl.ringOfIntegers p K) (L v)] [∀ v, Module.Free (PadicAlgCl.ringOfIntegers p K) (L v)] [∀ v, Module.Finite (PadicAlgCl.ringOfIntegers p K) (L v)]
    (t' : ∀ v, L (v + 1) →ₐc[(PadicAlgCl.ringOfIntegers p K)] L v) (ι : ∀ v, L v →ₐc[(PadicAlgCl.ringOfIntegers p K)] B (i₀ + v))
    (hιinj : ∀ v, Function.Injective (ι v))
    (hιrange : ∀ v, (ι v : L v →ₐ[(PadicAlgCl.ringOfIntegers p K)] B (i₀ + v)).range =
        HopfAlgebra.hopfKer (PDivisibleGroup.Tower.transitionLE t i₀ v))
    (hιt : ∀ v, (ι v).comp (t' v) = (t (i₀ + v)).comp (ι (v + 1))) :
    ∃ φ : ∀ v : ℕ, G.level v →ₐc[(PadicAlgCl.ringOfIntegers p K)] L v,
      (∀ v, (φ v).comp (G.transition v) = (t' v).comp (φ (v + 1))) ∧
      (∀ v, ∀ γ γ' : L v →ₐ[(PadicAlgCl.ringOfIntegers p K)] PadicAlgCl p,
        γ.comp (φ v : G.level v →ₐ[(PadicAlgCl.ringOfIntegers p K)] L v) = γ'.comp (φ v : G.level v →ₐ[(PadicAlgCl.ringOfIntegers p K)] L v) → γ = γ') ∧
      (∀ (v : ℕ) (y : G.level v →ₐ[(PadicAlgCl.ringOfIntegers p K)] PadicAlgCl p),
        (∃ γ : L v →ₐ[(PadicAlgCl.ringOfIntegers p K)] PadicAlgCl p, γ.comp (φ v : G.level v →ₐ[(PadicAlgCl.ringOfIntegers p K)] L v) = y) ↔
          ∃ x ∈ M, G.pointsMkAdd (PadicAlgCl p) v (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom y)) =
            (x : ℕ → G.Points (PadicAlgCl p)) v) := by sorry
