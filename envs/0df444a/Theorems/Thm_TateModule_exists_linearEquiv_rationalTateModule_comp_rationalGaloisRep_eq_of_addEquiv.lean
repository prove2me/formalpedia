-- Prove2me | Theorems.Thm_TateModule_exists_linearEquiv_rationalTateModule_comp_rationalGaloisRep_eq_of_addEquiv
-- name    : TateModule.exists_linearEquiv_rationalTateModule_comp_rationalGaloisRep_eq_of_addEquiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/64daf8fe-6f13-5b0e-94db-45282c874d70
-- title:
--   Functoriality of the rational Tate module under a group isomorphism
-- statement:
--   Let $p$ be a prime, let $J$ and $J'$ be abelian groups and let $\Psi : J \simeq J'$ be an isomorphism of additive groups; let $G$ and $G'$ be monoids acting distributively on $J$ and on $J'$ respectively. Here $T_p J$ denotes the subgroup [`TateModule p J`](def/EllipticCurve_TateModule.html#L15) of sequences $x : \mathbb{N} \to J$ satisfying $p^n \cdot x_n = 0$ and $p \cdot x_{n+1} = x_n$ for all $n$, with $\mathbb{Z}_p$-module structure, `proj p J n` the evaluation $x \mapsto x_n$, and `RationalTateModule p J` the base change $\mathbb{Q}_p \otimes_{\mathbb{Z}_p} T_p J$; `rationalGaloisRep p J G` is the monoid homomorphism sending $g \in G$ to the $\mathbb{Q}_p$-linear endomorphism obtained by base change from the levelwise action $x \mapsto (g \cdot x_n)_n$ of $g$ on $T_p J$. The assertion is that there exists a $\mathbb{Q}_p$-linear isomorphism $\Theta : \mathbb{Q}_p \otimes_{\mathbb{Z}_p} T_p J \to \mathbb{Q}_p \otimes_{\mathbb{Z}_p} T_p J'$ such that, first, for every $x \in T_p J$ there is $y \in T_p J'$ with $\Theta(1 \otimes x) = 1 \otimes y$ and $y_n = \Psi(x_n)$ for all $n$; and second, for all $g \in G$ and $g' \in G'$ with $\Psi(g \cdot z) = g' \cdot \Psi(z)$ for all $z \in J$, the underlying linear maps satisfy $\Theta \circ \mathrm{rationalGaloisRep}(g) = \mathrm{rationalGaloisRep}(g') \circ \Theta$.
--
--   This is the functoriality of the rational Tate module $V_p = \mathbb{Q}_p \otimes_{\mathbb{Z}_p} T_p$ for an isomorphism of the underlying abelian groups, together with the statement that the induced isomorphism intertwines operators corresponding under $\Psi$; the pinning on pure tensors identifies $\Theta$ as the map induced levelwise by $\Psi$. It is used to transport representations on Tate modules of Jacobians along an isomorphism of the groups carrying them, for instance in [`DrinfeldCurve.exists_linearEquiv_tateProd_comp_tateProdRep_eq_of_algEquiv`](thm.html#DrinfeldCurve.exists_linearEquiv_tateProd_comp_tateProdRep_eq_of_algEquiv).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_TateModule_exists_linearEquiv_rationalTateModule_comp_rationalGaloisRep_eq_of_addEquiv.lean

import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_ModularCurve_JZeroTateModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

open scoped TensorProduct

theorem TateModule.exists_linearEquiv_rationalTateModule_comp_rationalGaloisRep_eq_of_addEquiv
    (p : ℕ) [Fact p.Prime] {J J' : Type} [AddCommGroup J] [AddCommGroup J'] (Ψ : J ≃+ J')
    (G G' : Type) [Monoid G] [Monoid G'] [DistribMulAction G J] [DistribMulAction G' J'] :
    ∃ Θ : ModularCurve.RationalTateModule p J ≃ₗ[ℚ_[p]] ModularCurve.RationalTateModule p J',
      (∀ x : TateModule p J, ∃ y : TateModule p J',
        Θ ((1 : ℚ_[p]) ⊗ₜ[ℤ_[p]] x) = (1 : ℚ_[p]) ⊗ₜ[ℤ_[p]] y ∧
          ∀ n : ℕ, TateModule.proj p J' n y = Ψ (TateModule.proj p J n x)) ∧
      ∀ (g : G) (g' : G'), (∀ x : J, Ψ (g • x) = g' • Ψ x) →
        (Θ : ModularCurve.RationalTateModule p J →ₗ[ℚ_[p]] ModularCurve.RationalTateModule p J') ∘ₗ
            ModularCurve.rationalGaloisRep p J G g =
          ModularCurve.rationalGaloisRep p J' G' g' ∘ₗ
            (Θ : ModularCurve.RationalTateModule p J →ₗ[ℚ_[p]] ModularCurve.RationalTateModule p J') := by sorry
