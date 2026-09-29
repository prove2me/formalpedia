-- Prove2me | Theorems.Thm_Rep_exists_preIota_eq_map_extInflR_zero_of_exists_preIota_eq_of_pit
-- name    : Rep.exists_preIota_eq_map_extInflR_zero_of_exists_preIota_eq_of_pit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/a442051d-3233-5c72-9931-392e26006d4a
-- title:
--   Inflation of a vanishing Ext¹ relation-module class
-- statement:
--   Let $\pi\colon G'\to G$ be a homomorphism of finite groups, let $B$ be an object of `Rep ℤ G`, and let $p$ be a prime with $p\cdot b=0$ for every $b\in B$. Let $T$ be a short complex in `Rep ℤ G` and $T'$ one in `Rep ℤ G'`, both assumed short exact, with $T.X_3$ and $T'.X_3$ finite, and let $\varphi_1,\varphi_2,\varphi_3$ be morphisms $\mathrm{Res}_\pi T.X_i\to T'.X_i$ making the two squares commute ($w_1$ for the monomorphisms, $w_2$ for the epimorphisms). Assume (`hpit`) that $\varphi_3$ annihilates every $p$-power-torsion element of $T.X_3$. Write $R(B)$ for the project's integral relation module [`Rep.relationModuleInt B`](def/GroupCohomology_RelationModule.html#L73), the kernel of the free cover $\mathbb Z[G]^{(B)}\to B$ with its $G$-action, and recall that degree-zero cohomology of an internal hom object is the module of $G$-equivariant maps. Let $z$ be a class in $H^0$ of $\mathrm{Hom}(R(B),T.X_1)$ and suppose its pushforward along $T.f$ into $H^0$ of $\mathrm{Hom}(R(B),T.X_2)$ is the restriction along $R(B)\hookrightarrow\mathbb Z[G]^{(B)}$ (the map induced by [`Rep.preι B T.X₂`](def/GroupCohomology_RelationHomDefect.html#L50)) of a class $\psi$ in $H^0$ of $\mathrm{Hom}(\mathbb Z[G]^{(B)},T.X_2)$. The conclusion is that there is a class $\psi'$ in $H^0$ of $\mathrm{Hom}(\mathbb Z[G']^{(\mathrm{Res}_\pi B)},T'.X_1)$ whose restriction along $R(\mathrm{Res}_\pi B)\hookrightarrow\mathbb Z[G']^{(\mathrm{Res}_\pi B)}$ equals the image of $z$ under [`Rep.extInflR π B T.X₁ T'.X₁ φ₁`](def/GroupCohomology_RelationHomDefect.html#L72), that is, under the composite of the identification of the restriction of $\mathrm{Hom}(R(B),T.X_1)$ with $\mathrm{Hom}(\mathrm{Res}_\pi R(B),\mathrm{Res}_\pi T.X_1)$, precomposition with [`Rep.relationModuleInt.resMap π B`](def/GroupCohomology_RelationModuleRes.html#L52) $\colon R(\mathrm{Res}_\pi B)\to \mathrm{Res}_\pi R(B)$, and pushforward along $\varphi_1$.
--
--   In the cocycle presentation of $\mathrm{Ext}^1$ by equivariant maps out of a relation module, this says that a class over $G$ which dies in $\mathrm{Ext}^1_G(B,T.X_2)$ has inflation–restriction image over $G'$ that is again split, i.e. comes from the free cover; the hypothesis on $\varphi_3$ is the algebraic shape of a principal-ideal-theorem ($p$-capitulation) input. It is used in the Poitou–Tate style duality computations, by [`groupCohomology.exists_mem_continuousH1S_locRes_eq_of_forall_sum_theta_eq_zero_arch_of_ne_two`](thm.html#groupCohomology.exists_mem_continuousH1S_locRes_eq_of_forall_sum_theta_eq_zero_arch_of_ne_two) and [`groupCohomology.exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two`](thm.html#groupCohomology.exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_exists_preIota_eq_map_extInflR_zero_of_exists_preIota_eq_of_pit.lean

import Mathlib
import Definitions.Def_GroupCohomology_RelationModule
import Definitions.Def_GroupCohomology_RelationModuleRes
import Definitions.Def_GroupCohomology_RepCokernel
import Definitions.Def_GroupCohomology_RepImage
import Definitions.Def_GroupCohomology_RelationHomDefect

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory

theorem Rep.exists_preIota_eq_map_extInflR_zero_of_exists_preIota_eq_of_pit
    {G G' : Type} [Group G] [Group G'] [Fintype G] [Fintype G'] (π : G' →* G) (B : Rep ℤ G) (p : ℕ) [Fact p.Prime] (hB : ∀ b : B, p • b = 0)
    {T : ShortComplex (Rep ℤ G)} (hT : T.ShortExact) {T' : ShortComplex (Rep ℤ G')} (hT' : T'.ShortExact) [Finite T.X₃] [Finite T'.X₃]
    (φ₁ : Rep.res π T.X₁ ⟶ T'.X₁) (φ₂ : Rep.res π T.X₂ ⟶ T'.X₂) (φ₃ : Rep.res π T.X₃ ⟶ T'.X₃)
    (w₁ : (Rep.resFunctor π).map T.f ≫ φ₂ = φ₁ ≫ T'.f) (w₂ : (Rep.resFunctor π).map T.g ≫ φ₃ = φ₂ ≫ T'.g)
    (hpit : ∀ c : T.X₃, (∃ k : ℕ, p ^ k • c = 0) → φ₃.hom c = 0)
    (z : groupCohomology ((ihom (Rep.relationModuleInt B)).obj T.X₁) 0)
    (hz : ∃ ψ : groupCohomology ((ihom (Rep.free ℤ G B)).obj T.X₂) 0,
      (groupCohomology.map (MonoidHom.id G) (Rep.preι B T.X₂) 0).hom ψ =
        (groupCohomology.map (MonoidHom.id G) ((ihom (Rep.relationModuleInt B)).map T.f) 0).hom z) :
    ∃ ψ' : groupCohomology ((ihom (Rep.free ℤ G' (Rep.res π B))).obj T'.X₁) 0,
      (groupCohomology.map (MonoidHom.id G') (Rep.preι (Rep.res π B) T'.X₁) 0).hom ψ' =
        (groupCohomology.map π (Rep.extInflR π B T.X₁ T'.X₁ φ₁) 0).hom z := by sorry
