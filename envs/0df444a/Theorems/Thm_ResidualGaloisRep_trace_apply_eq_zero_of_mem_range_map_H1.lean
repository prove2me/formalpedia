-- Prove2me | Theorems.Thm_ResidualGaloisRep_trace_apply_eq_zero_of_mem_range_map_H1
-- name    : ResidualGaloisRep.trace_apply_eq_zero_of_mem_range_map_H1
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:01.535489+00:00
-- url     : https://prove2.me/theorems/aecc95bd-f902-5348-a17e-6f2ac0c42f02
-- title:
--   Trace vanishing for cocycles coming from ad⁰ρ̄
-- statement:
--   Let $k$ be a field and let $\bar\rho$ be a residual Galois representation over $k$, i.e. a $k$-vector space $V$ with $\dim_k V = 2$ together with a monoid homomorphism $\rho\colon \operatorname{Gal}(\overline{\mathbb Q}/\mathbb Q)\to \operatorname{End}_k(V)$ that is trivial on the subgroup fixing some finite-dimensional intermediate field of $\overline{\mathbb Q}/\mathbb Q$ pointwise. Write $\mathrm{ad}\,\bar\rho$ for the representation of $\operatorname{Gal}(\overline{\mathbb Q}/\mathbb Q)$ on $\operatorname{End}_k(V)$ given by $\sigma\mapsto(g\mapsto \rho(\sigma)\,g\,\rho(\sigma^{-1}))$, and $\mathrm{ad}^0\bar\rho$ for its subrepresentation on $\ker(\operatorname{tr}_k V)$. Let $G$ be a group and $f\colon G\to\operatorname{Gal}(\overline{\mathbb Q}/\mathbb Q)$ a group homomorphism, and let $\varphi$ be a morphism of $G$-representations from the restriction along $f$ of $\mathrm{ad}^0\bar\rho$ to the restriction along $f$ of $\mathrm{ad}\,\bar\rho$ whose underlying linear map sends each $x\in\ker(\operatorname{tr}_k V)$ to $x$ viewed in $\operatorname{End}_k(V)$, that is, $\varphi$ is the inclusion. Let $c$ be a $1$-cocycle of the restricted representation $\mathrm{ad}\,\bar\rho|_G$ whose class in $H^1$ lies in the image of the map on $H^1$ induced by the identity of $G$ and $\varphi$. Then $\operatorname{tr}\big(c(\sigma)\big)=0$ for every $\sigma\in G$.
--
--   This is the easy half of the decomposition $H^1(G,\mathrm{ad}\,\bar\rho)=H^1(G,\mathrm{ad}^0\bar\rho)\oplus H^1(G,k)$: composing a cocycle with the trace annihilates the image of $H^1(G,\mathrm{ad}^0\bar\rho)$, no hypothesis on the characteristic of $k$ being needed. It is used in the comparison of dimensions of local flat deformation classes for $\mathrm{ad}^0\bar\rho$ and for $\mathrm{ad}\,\bar\rho$, in the form of the statement [`ResidualGaloisRep.finrank_localFlatClasses_add_one_le_finrank_localFlatClassesAd`](thm.html#ResidualGaloisRep.finrank_localFlatClasses_add_one_le_finrank_localFlatClassesAd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ResidualGaloisRep_trace_apply_eq_zero_of_mem_range_map_H1.lean

import Mathlib
import Definitions.Def_GaloisRep_AdZero

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory groupCohomology

theorem ResidualGaloisRep.trace_apply_eq_zero_of_mem_range_map_H1
    {k : Type} [Field k] (ρbar : ResidualGaloisRep k)
    {G : Type} [Group G] (f : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (φ : Rep.res f ρbar.adZero ⟶ Rep.res f (Rep.of ρbar.adRep))
    (hφ : ∀ x : LinearMap.ker (LinearMap.trace k ρbar.V), φ.hom x = (x : Module.End k ρbar.V))
    (c : cocycles₁ (Rep.res f (Rep.of ρbar.adRep)))
    (hc : (H1π (Rep.res f (Rep.of ρbar.adRep))).hom c ∈
      LinearMap.range (groupCohomology.map (A := Rep.res f ρbar.adZero) (MonoidHom.id G) φ 1).hom)
    (σ : G) :
    LinearMap.trace k ρbar.V ((c : G → Module.End k ρbar.V) σ) = 0 := by sorry
