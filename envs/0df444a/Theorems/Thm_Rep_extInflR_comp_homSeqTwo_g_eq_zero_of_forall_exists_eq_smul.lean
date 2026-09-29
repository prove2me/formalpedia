-- Prove2me | Theorems.Thm_Rep_extInflR_comp_homSeqTwo_g_eq_zero_of_forall_exists_eq_smul
-- name    : Rep.extInflR_comp_homSeqTwo_g_eq_zero_of_forall_exists_eq_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/8b748e92-c19a-55a9-9800-a81ef060a2b1
-- title:
--   Vanishing of the Hom-defect map when pB=0 and φ(E)⊆ pE'
-- statement:
--   Let $\pi\colon G'\to G$ be a homomorphism of groups, let $B$ and $E$ be $\mathbb{Z}$-linear representations of $G$ with the underlying set of $B$ finite, let $E'$ be a $\mathbb{Z}$-linear representation of $G'$, and let $\varphi\colon \mathrm{Res}_\pi E\to E'$ be a morphism of representations of $G'$. Let $p$ be a prime, assume that $p\cdot b=0$ for every $b\in B$, and assume that every element of the image of $\varphi$ is a $p$-th multiple, i.e. for each $e\in E$ there is $e'\in E'$ with $\varphi(e)=p\cdot e'$ (no $\mathbb{Z}$-linear $p$-th root of $\varphi$ is required). Write $R_G(B)=$ [`Rep.relationModuleInt B`](def/GroupCohomology_RelationModule.html#L73) for the relation module of the canonical free presentation of $B$, and let [`Rep.extInflR π B E E' φ`](def/GroupCohomology_RelationHomDefect.html#L72) be the morphism $\mathrm{Res}_\pi\,\underline{\mathrm{Hom}}(R_G(B),E)\to\underline{\mathrm{Hom}}(R_{G'}(\mathrm{Res}_\pi B),E')$ given on elements by $h\mapsto \varphi\circ h\circ \rho$, where $\rho=$ [`Rep.relationModuleInt.resMap π B`](def/GroupCohomology_RelationModuleRes.html#L52) is the comparison map $R_{G'}(\mathrm{Res}_\pi B)\to \mathrm{Res}_\pi R_G(B)$ induced by the map of free covers (the identification [`Rep.resIhom`](def/GroupCohomology_RelationModuleRes.html#L39) of the restricted internal Hom with the internal Hom of restrictions being the identity on underlying maps). The assertion is that [`Rep.extInflR π B E E' φ`](def/GroupCohomology_RelationHomDefect.html#L72) followed by the morphism `g` of the short complex [`Rep.homSeq₂ (Rep.res π B) E'`](def/GroupCohomology_RelationHomDefect.html#L64), which issues from $\underline{\mathrm{Hom}}(R_{G'}(\mathrm{Res}_\pi B),E')$, is the zero morphism.
--
--   This is the module-level form of the statement that the defect measuring non-extendability of homomorphisms out of the relation module — the group-theoretic incarnation of $\mathrm{Ext}^1_{\mathbb{Z}}(B,\cdot)$ for a $B$ killed by $p$ — dies after a change of group along which the coefficient map $\varphi$ becomes divisible by $p$ pointwise. It is used in [`NumberField.SUnits.exists_level_forall_map_extInflR_eq_zero_of_isGlobalBridge2_apply_eq_zero`](thm.html#NumberField.SUnits.exists_level_forall_map_extInflR_eq_zero_of_isGlobalBridge2_apply_eq_zero), where such a level is produced for $S$-unit coefficient modules in a tower.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_extInflR_comp_homSeqTwo_g_eq_zero_of_forall_exists_eq_smul.lean

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

theorem Rep.extInflR_comp_homSeqTwo_g_eq_zero_of_forall_exists_eq_smul
    {G G' : Type} [Group G] [Group G'] (π : G' →* G) (B E : Rep ℤ G) [Fintype B] (E' : Rep ℤ G') (φ : Rep.res π E ⟶ E')
    (p : ℕ) [Fact p.Prime] (hB : ∀ b : B, p • b = 0) (hφ : ∀ e : E, ∃ e' : E', φ.hom e = p • e') :
    Rep.extInflR π B E E' φ ≫ (Rep.homSeq₂ (Rep.res π B) E').g = 0 := by sorry
