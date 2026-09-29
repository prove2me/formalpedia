-- Prove2me | Theorems.Thm_PDivisibleGroup_CartierDuality_exists_linearIndependent_invariant_dual_padicComplex_tateModule_of_hasDimension_of_ringOfIntegers
-- name    : PDivisibleGroup.CartierDuality.exists_linearIndependent_invariant_dual_padicComplex_tateModule_of_hasDimension_of_ringOfIntegers
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:58.387243+00:00
-- url     : https://prove2.me/theorems/05d11ee4-bdb0-5ee9-a9f4-6d92162e10c9
-- title:
--   Tate's period functionals: n invariant ℂₚ-functionals on the dual Tate module
-- statement:
--   Let $p$ be a prime and let $K$ be an intermediate field of $\mathbb{Q}_p \subseteq \overline{\mathbb{Q}}_p$ (the algebraic closure `PadicAlgCl p`) which is finite-dimensional over $\mathbb{Q}_p$; write $\mathcal{O}_K$ for [`PadicAlgCl.ringOfIntegers p K`](def/PadicAlgCl_RingOfIntegers.html#L11), the intersection of the integral closure of $\mathbb{Z}_p$ in $\overline{\mathbb{Q}}_p$ with $K$, viewed as a $\mathbb{Z}_p$-subalgebra. Let $G$ and $G'$ be $p$-divisible groups of height $h$ over $\mathcal{O}_K$, each given by commutative cocommutative Hopf algebras `level v` that are finite free $\mathcal{O}_K$-modules of rank $p^{vh}$ together with surjective bialgebra transition maps whose kernels are the $p^v$-torsion ideals, and let $D$ be a Cartier duality datum between them, i.e. coalgebra-algebra isomorphisms $G'.\mathrm{level}\,v \simeq \mathrm{CartierDual}\,(G.\mathrm{level}\,v)$ compatible with the transition maps up to multiplication by $p$. Assume $G$ has dimension $n$ in the sense that for every $v$ the cotangent module $G.\mathrm{Cotangent}\,v$ is $\mathcal{O}_K$-linearly isomorphic to $(\mathcal{O}_K/(p^v))^n$. Put $W' = \mathbb{C}_p \otimes_{\mathbb{Q}_p} (\mathbb{Q}_p \otimes_{\mathbb{Z}_p} T')$, where $T' =$ [`TateModule p (G'.Points (PadicAlgCl p))`](def/EllipticCurve_TateModule.html#L15) is the group of sequences $(x_v)$ of $\overline{\mathbb{Q}}_p$-points of $G'$ (the direct limit of the level point groups) satisfying $p^v x_v = 0$ and $p\,x_{v+1} = x_v$. Then there is a family $\varphi : \mathrm{Fin}\,n \to \mathrm{Hom}_{\mathbb{C}_p}(W', \mathbb{C}_p)$ which is linearly independent over $\mathbb{C}_p$ and such that for every $\mathbb{Q}_p$-algebra automorphism $\sigma$ of $\overline{\mathbb{Q}}_p$ and every $\mathcal{O}_K$-algebra automorphism $\tau$ of $\overline{\mathbb{Q}}_p$ with $\tau x = \sigma x$ for all $x$, and for every $j$ and every $x \in W'$, one has $\varphi_j\big((\sigma \otimes \tau)(x)\big) = \sigma \cdot \varphi_j(x)$; here $\sigma$ acts on the factor $\mathbb{C}_p$ through its continuous extension [`PadicComplex.galAlgHom p σ`](def/PadicComplex_GaloisAction.html#L73) and $\tau$ acts on $\mathbb{Q}_p \otimes_{\mathbb{Z}_p} T'$ by base change of the entrywise action `G'.tateModuleRep` on the Tate module.
--
--   This is Tate's Proposition 11 on $p$-divisible groups over the ring of integers of a finite extension of $\mathbb{Q}_p$: the period map attached to the cotangent space of $G$ produces, for $G$ of dimension $n$, exactly $n$ independent Galois-invariant $\mathbb{C}_p$-valued functionals on the $\mathbb{C}_p$-vector space built from the Tate module of the Cartier dual $G'$. It is the analytic input to the construction of a basis of $\mathbb{C}_p \otimes T'$ on which the Galois action is given by powers of the cyclotomic character, i.e. to the Hodge–Tate decomposition of the Tate module.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PDivisibleGroup_CartierDuality_exists_linearIndependent_invariant_dual_padicComplex_tateModule_of_hasDimension_of_ringOfIntegers.lean

import Mathlib
import Definitions.Def_PadicComplex_GaloisAction
import Definitions.Def_PDivisibleGroup_CartierDuality
import Definitions.Def_PDivisibleGroup_Dimension
import Definitions.Def_PadicAlgCl_RingOfIntegers

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem PDivisibleGroup.CartierDuality.exists_linearIndependent_invariant_dual_padicComplex_tateModule_of_hasDimension_of_ringOfIntegers
    (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    {h : ℕ} {G G' : PDivisibleGroup (PadicAlgCl.ringOfIntegers p K) p h} (D : G.CartierDuality G')
    {n : ℕ} (hn : G.HasDimension n) :
    ∃ φ : Fin n →
        (ℂ_[p] ⊗[ℚ_[p]] (ℚ_[p] ⊗[ℤ_[p]] TateModule p (G'.Points (PadicAlgCl p))) →ₗ[ℂ_[p]] ℂ_[p]),
      LinearIndependent ℂ_[p] φ ∧
      ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
        (τ : PadicAlgCl p ≃ₐ[PadicAlgCl.ringOfIntegers p K] PadicAlgCl p),
        (∀ x : PadicAlgCl p, τ x = σ x) → ∀ (j : Fin n)
        (x : ℂ_[p] ⊗[ℚ_[p]] (ℚ_[p] ⊗[ℤ_[p]] TateModule p (G'.Points (PadicAlgCl p)))),
        φ j (TensorProduct.map (PadicComplex.galAlgHom p σ).toLinearMap
            ((G'.tateModuleRep (PadicAlgCl p) τ).baseChange ℚ_[p]) x) =
          σ • φ j x := by sorry
