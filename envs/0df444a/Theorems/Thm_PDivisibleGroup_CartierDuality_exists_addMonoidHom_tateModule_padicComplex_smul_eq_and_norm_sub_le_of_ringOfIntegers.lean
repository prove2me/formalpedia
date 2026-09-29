-- Prove2me | Theorems.Thm_PDivisibleGroup_CartierDuality_exists_addMonoidHom_tateModule_padicComplex_smul_eq_and_norm_sub_le_of_ringOfIntegers
-- name    : PDivisibleGroup.CartierDuality.exists_addMonoidHom_tateModule_padicComplex_smul_eq_and_norm_sub_le_of_ringOfIntegers
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:58.387243+00:00
-- url     : https://prove2.me/theorems/102d2139-67f9-5a87-b56a-009f33f9065b
-- title:
--   Existence of Tate's period maps dαⱼ over 𝒪_K
-- statement:
--   Let $p$ be a prime, let $K$ be an intermediate field between $\mathbb{Q}_p$ and $\overline{\mathbb{Q}}_p$ with $[K:\mathbb{Q}_p]$ finite, and let $\mathcal{O}_K$ be [`PadicAlgCl.ringOfIntegers p K`](def/PadicAlgCl_RingOfIntegers.html#L11), the intersection of the integral closure of $\mathbb{Z}_p$ in $\overline{\mathbb{Q}}_p$ with $K$. Let $G,G'$ be $p$-divisible groups of height $h$ over $\mathcal{O}_K$ (families of finite free cocommutative Hopf algebras `level v` of rank $p^{vh}$ with surjective transition maps whose kernels are the $p^v$-torsion ideals), let $D$ be a Cartier duality datum identifying each $G'_v$ with the Cartier dual of $G_v$ compatibly with the transitions and multiplication by $p$, assume $G$ has dimension $n$ (each $G$-cotangent module at level $v$ is isomorphic to $(\mathcal{O}_K/(p^v))^n$), and fix an $\mathcal{O}_K$-basis $b$ indexed by `Fin n` of the cotangent module $\omega_G$ of compatible families of cotangent vectors. Then there are additive maps $d\alpha_j \colon T_p(G'(\overline{\mathbb{Q}}_p)) \to \mathbb{C}_p$, for $j \in$ `Fin n`, where the Tate module consists of sequences $(y_v)$ of points of $G'$ over $\overline{\mathbb{Q}}_p$ with $p^v y_v = 0$ and $p\,y_{v+1} = y_v$, such that: (i) $d\alpha_j(a\,y) = a\,d\alpha_j(y)$ for $a \in \mathbb{Z}_p$, via $\mathbb{Z}_p \to \mathbb{Q}_p \subseteq \mathbb{C}_p$; (ii) for every $\sigma \in \mathrm{Gal}(\overline{\mathbb{Q}}_p/\mathbb{Q}_p)$ and every automorphism $\tau$ of $\overline{\mathbb{Q}}_p$ over $\mathcal{O}_K$ agreeing pointwise with $\sigma$, one has $d\alpha_j(\tau y) = \sigma \cdot d\alpha_j(y)$, the action of $\tau$ on the Tate module being the one induced functorially on points; and (iii) writing $\mathcal{O}$ for the integral closure of $\mathcal{O}_K$ in $\overline{\mathbb{Q}}_p$, if $\psi$ is a point of $G'$ at level $v$ with values in $\mathcal{O}$ whose image in the direct limit of points over $\overline{\mathbb{Q}}_p$ is the $v$-th component of $y$, and if $z \in \mathcal{O} \otimes_{\mathcal{O}_K} \omega_G$ has image $D.\mathrm{charDiff}\,v\,\psi$ under the projection $\omega_G \to \omega_{G_v}$ tensored with $\mathcal{O}$, then $\|d\alpha_j(y) - (b^j \otimes \mathrm{id})(z)\| \le p^{-v}$, the element $(b^j \otimes \mathrm{id})(z) \in \mathcal{O}$ being viewed in $\overline{\mathbb{Q}}_p \subseteq \mathbb{C}_p$ through the right unitor.
--
--   This is the existence part of Tate's construction of the period maps attached to a $p$-divisible group over the ring of integers of a finite extension of $\mathbb{Q}_p$: the coordinates $d\alpha_j$ of the map $T_p(G') \to \mathbb{C}_p^{\,n}$ obtained by passing to the limit over the differentials at the origin of the characters of $G_v$ cut out by Cartier duality, with levelwise approximation accurate to $p^{-v}$. It is used to produce a Galois-equivariant linearly independent system of $\mathbb{C}_p$-valued functionals on the Tate module.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PDivisibleGroup_CartierDuality_exists_addMonoidHom_tateModule_padicComplex_smul_eq_and_norm_sub_le_of_ringOfIntegers.lean

import Mathlib
import Definitions.Def_PadicComplex_GaloisAction
import Definitions.Def_PDivisibleGroup_CharacterDifferential
import Definitions.Def_PadicAlgCl_RingOfIntegers

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct in

theorem PDivisibleGroup.CartierDuality.exists_addMonoidHom_tateModule_padicComplex_smul_eq_and_norm_sub_le_of_ringOfIntegers
    (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    {h : ℕ} {G G' : PDivisibleGroup (PadicAlgCl.ringOfIntegers p K) p h} (D : G.CartierDuality G')
    {n : ℕ} (hn : G.HasDimension n)
    (b : Module.Basis (Fin n) (PadicAlgCl.ringOfIntegers p K) G.cotangentModule) :
    ∃ dα : Fin n → (TateModule p (G'.Points (PadicAlgCl p)) →+ ℂ_[p]),
      (∀ (j : Fin n) (a : ℤ_[p]) (y : TateModule p (G'.Points (PadicAlgCl p))),
          dα j (a • y) = (a : ℚ_[p]) • dα j y) ∧
      (∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
          (τ : PadicAlgCl p ≃ₐ[PadicAlgCl.ringOfIntegers p K] PadicAlgCl p),
          (∀ x : PadicAlgCl p, τ x = σ x) →
          ∀ (j : Fin n) (y : TateModule p (G'.Points (PadicAlgCl p))),
          dα j (G'.tateModuleRep (PadicAlgCl p) τ y) = σ • dα j y) ∧
      (∀ (j : Fin n) (y : TateModule p (G'.Points (PadicAlgCl p))) (v : ℕ)
          (ψ : G'.Point (integralClosure (PadicAlgCl.ringOfIntegers p K) (PadicAlgCl p)) v),
          G'.pointsMkAdd (PadicAlgCl p) v
              (Additive.ofMul (G'.pointMap
                (integralClosure (PadicAlgCl.ringOfIntegers p K) (PadicAlgCl p)).val v ψ)) =
            (y : ℕ → G'.Points (PadicAlgCl p)) v →
          ∀ z : integralClosure (PadicAlgCl.ringOfIntegers p K) (PadicAlgCl p)
              ⊗[PadicAlgCl.ringOfIntegers p K] G.cotangentModule,
            (G.cotangentModuleProj v).lTensor
                (integralClosure (PadicAlgCl.ringOfIntegers p K) (PadicAlgCl p)) z =
              D.charDiff (integralClosure (PadicAlgCl.ringOfIntegers p K) (PadicAlgCl p)) v ψ →
            ‖dα j y - ((TensorProduct.rid (PadicAlgCl.ringOfIntegers p K)
                (integralClosure (PadicAlgCl.ringOfIntegers p K) (PadicAlgCl p))
                ((b.coord j).lTensor
                  (integralClosure (PadicAlgCl.ringOfIntegers p K) (PadicAlgCl p)) z) :
                  PadicAlgCl p) : ℂ_[p])‖ ≤
              (p : ℝ) ^ (-(v : ℤ))) := by sorry
