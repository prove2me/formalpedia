-- Prove2me | Theorems.Thm_Rep_exists_resMap_comp_eq_comp_add_iota_comp_of_pit
-- name    : Rep.exists_resMap_comp_eq_comp_add_iota_comp_of_pit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/5239cdbd-2ce2-52bd-b426-5e2b33a571ba
-- title:
--   Lifting a relation-module map after restriction, cokernel form
-- statement:
--   Let $G$ and $G'$ be finite groups and $\pi\colon G'\to G$ a group homomorphism, let $B$ be an object of `Rep ℤ G`, and let $p$ be a prime such that $p\cdot b=0$ for every $b\in B$. Let $T=(T.X_1\xrightarrow{f}T.X_2\xrightarrow{g}T.X_3)$ be a short complex in `Rep ℤ G` and $T'$ one in `Rep ℤ G'`, both short exact, with $T.X_3$ and $T'.X_3$ finite. Let $\varphi_1,\varphi_2,\varphi_3$ be morphisms from the restrictions along $\pi$ of $T.X_1,T.X_2,T.X_3$ to $T'.X_1,T'.X_2,T'.X_3$ satisfying the two commutation relations $\mathrm{res}(f)$ followed by $\varphi_2$ equals $\varphi_1$ followed by $T'.f$, and $\mathrm{res}(g)$ followed by $\varphi_3$ equals $\varphi_2$ followed by $T'.g$, and assume $\varphi_3$ annihilates every $p$-power-torsion element of $T.X_3$. Write $R(B)$ for the relation module of $B$, the kernel of the free cover $\mathbb{Z}[G]^{(B)}\to B$ viewed as a $\mathbb{Z}[G]$-representation. Then for every morphism $t\colon R(B)\to T.X_2$ there exist $t'\colon R(\mathrm{res}_\pi B)\to T'.X_1$ and $\chi\colon \mathbb{Z}[G']^{(\mathrm{res}_\pi B)}\to T'.X_2$ such that the change-of-group map [`Rep.relationModuleInt.resMap`](def/GroupCohomology_RelationModuleRes.html#L52) $\pi$ $B$, followed by $\mathrm{res}(t)$ and then $\varphi_2$, equals $t'$ followed by $T'.f$ plus the inclusion $R(\mathrm{res}_\pi B)\hookrightarrow \mathbb{Z}[G']^{(\mathrm{res}_\pi B)}$ followed by $\chi$.
--
--   In Ext-theoretic terms this says that, once the $p$-primary part of the finite quotient $T.X_3$ is killed by $\varphi_3$ (the capitulation, or principal-ideal-theorem, hypothesis), the inflation–restriction image of the class of $t$ in $\mathrm{Ext}^1_{G'}(\mathrm{res}_\pi B,T'.X_2)$ already comes from $\mathrm{Ext}^1_{G'}(\mathrm{res}_\pi B,T'.X_1)$, the equality with $\chi$ expressing that the two cocycles on the relation module differ by one extending to the free module. It is used in the construction of the nondegenerate pairing between the two Šafarevič–Tate style groups in [`groupCohomology.exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two`](thm.html#groupCohomology.exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_exists_resMap_comp_eq_comp_add_iota_comp_of_pit.lean

import Mathlib
import Definitions.Def_GroupCohomology_RelationModule
import Definitions.Def_GroupCohomology_RelationModuleRes

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory

theorem Rep.exists_resMap_comp_eq_comp_add_iota_comp_of_pit
    {G G' : Type} [Group G] [Group G'] [Fintype G] [Fintype G'] (π : G' →* G) (B : Rep ℤ G) (p : ℕ) [Fact p.Prime] (hB : ∀ b : B, p • b = 0)
    {T : ShortComplex (Rep ℤ G)} (hT : T.ShortExact) {T' : ShortComplex (Rep ℤ G')} (hT' : T'.ShortExact) [Finite T.X₃] [Finite T'.X₃]
    (φ₁ : Rep.res π T.X₁ ⟶ T'.X₁) (φ₂ : Rep.res π T.X₂ ⟶ T'.X₂) (φ₃ : Rep.res π T.X₃ ⟶ T'.X₃)
    (w₁ : (Rep.resFunctor π).map T.f ≫ φ₂ = φ₁ ≫ T'.f) (w₂ : (Rep.resFunctor π).map T.g ≫ φ₃ = φ₂ ≫ T'.g)
    (hpit : ∀ c : T.X₃, (∃ k : ℕ, p ^ k • c = 0) → φ₃.hom c = 0)
    (t : Rep.relationModuleInt B ⟶ T.X₂) :
    ∃ (t' : Rep.relationModuleInt (Rep.res π B) ⟶ T'.X₁) (χ : Rep.free ℤ G' (Rep.res π B) ⟶ T'.X₂),
      Rep.relationModuleInt.resMap π B ≫ (Rep.resFunctor π).map t ≫ φ₂ =
        t' ≫ T'.f + Rep.relationModuleInt.ι (Rep.res π B) ≫ χ := by sorry
