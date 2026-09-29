-- Prove2me | Theorems.Thm_TateModule_exists_rationalTateModule_linearEquiv_comp_rationalGaloisRep_eq_of_injective_of_card_torsionBy_eq
-- name    : TateModule.exists_rationalTateModule_linearEquiv_comp_rationalGaloisRep_eq_of_injective_of_card_torsionBy_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/f307223d-1bed-5d13-9e7f-239819560f9c
-- title:
--   Equivariant isomorphism of rational Tate modules from equal torsion counts
-- statement:
--   Let $J$ and $J'$ be additive commutative groups, each carrying a distributive action of a monoid $G$, and let $\beta : J \to J'$ be an additive homomorphism which is injective and satisfies $\beta(g \cdot x) = g \cdot \beta(x)$ for all $g \in G$ and $x \in J$. Let $\ell$ be a prime and $r$ a natural number, and assume that for every $n$ the subgroup of elements of $J$ annihilated by $\ell^n$ has cardinality $(\ell^n)^r$, and likewise for $J'$. Here [`TateModule ℓ J`](def/EllipticCurve_TateModule.html#L15) is the group of sequences $(x_n)_{n \in \mathbb{N}}$ in $J$ with $\ell^n x_n = 0$ and $\ell x_{n+1} = x_n$ for all $n$, a $\mathbb{Z}_\ell$-module, and [`ModularCurve.RationalTateModule ℓ J`](def/ModularCurve_JZeroTateModule.html#L45) is $\mathbb{Q}_\ell \otimes_{\mathbb{Z}_\ell} \mathrm{TateModule}\,\ell\,J$. The conclusion asserts the existence of a $\mathbb{Z}_\ell$-linear map $T$ from [`TateModule ℓ J`](def/EllipticCurve_TateModule.html#L15) to [`TateModule ℓ J'`](def/EllipticCurve_TateModule.html#L15) and a $\mathbb{Q}_\ell$-linear isomorphism $e$ of the corresponding rational Tate modules such that: $T$ acts coordinatewise by $\beta$, i.e. $(Tx)_n = \beta(x_n)$ for all $x$ and $n$; $e$ is the base change of $T$ along $\mathbb{Z}_\ell \to \mathbb{Q}_\ell$, that is $e(v) = (T \otimes \mathbb{Q}_\ell)(v)$ for every $v$; and for every $g \in G$ one has $e \circ \rho_J(g) = \rho_{J'}(g) \circ e$, where $\rho_J$ and $\rho_{J'}$ denote [`ModularCurve.rationalGaloisRep ℓ · G`](def/ModularCurve_JZeroTateModule.html#L48), the base change to $\mathbb{Q}_\ell$ of the coordinatewise action of $G$ on Tate modules.
--
--   This is the standard assertion that an injective equivariant homomorphism between groups whose $\ell$-power torsion subgroups have the same orders $\ell^{rn}$ induces an equivariant isomorphism of rational $\ell$-adic Tate modules, stated for an abstract monoid action rather than for a Galois action. It is used in the Drinfeld-curve part of the development, via [`DrinfeldCurve.exists_rationalTateModule_linearEquiv_baseChange_of_injective_of_card_torsionBy_eq`](thm.html#DrinfeldCurve.exists_rationalTateModule_linearEquiv_baseChange_of_injective_of_card_torsionBy_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_TateModule_exists_rationalTateModule_linearEquiv_comp_rationalGaloisRep_eq_of_injective_of_card_torsionBy_eq.lean

import Mathlib
import Definitions.Def_ModularCurve_JZeroTateModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem TateModule.exists_rationalTateModule_linearEquiv_comp_rationalGaloisRep_eq_of_injective_of_card_torsionBy_eq
    {J J' : Type} [AddCommGroup J] [AddCommGroup J'] {G : Type} [Monoid G] [DistribMulAction G J] [DistribMulAction G J']
    (β : J →+ J') (hβ : Function.Injective β) (hβG : ∀ (g : G) (x : J), β (g • x) = g • β x)
    (ℓ : ℕ) [Fact ℓ.Prime] (r : ℕ)
    (hJ : ∀ n : ℕ, Nat.card (Submodule.torsionBy ℤ J ((ℓ ^ n : ℕ) : ℤ)) = (ℓ ^ n) ^ r)
    (hJ' : ∀ n : ℕ, Nat.card (Submodule.torsionBy ℤ J' ((ℓ ^ n : ℕ) : ℤ)) = (ℓ ^ n) ^ r) :
    ∃ (T : TateModule ℓ J →ₗ[ℤ_[ℓ]] TateModule ℓ J')
      (e : ModularCurve.RationalTateModule ℓ J ≃ₗ[ℚ_[ℓ]] ModularCurve.RationalTateModule ℓ J'),
      (∀ (x : TateModule ℓ J) (n : ℕ), ((T x : TateModule ℓ J') : ℕ → J') n = β ((x : ℕ → J) n)) ∧
      (∀ v, e v = T.baseChange ℚ_[ℓ] v) ∧
      ∀ g : G, (e : ModularCurve.RationalTateModule ℓ J →ₗ[ℚ_[ℓ]] ModularCurve.RationalTateModule ℓ J') ∘ₗ
          ModularCurve.rationalGaloisRep ℓ J G g =
        ModularCurve.rationalGaloisRep ℓ J' G g ∘ₗ
          (e : ModularCurve.RationalTateModule ℓ J →ₗ[ℚ_[ℓ]] ModularCurve.RationalTateModule ℓ J') := by sorry
