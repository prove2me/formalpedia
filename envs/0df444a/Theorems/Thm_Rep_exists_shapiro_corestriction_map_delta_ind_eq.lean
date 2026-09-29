-- Prove2me | Theorems.Thm_Rep_exists_shapiro_corestriction_map_delta_ind_eq
-- name    : Rep.exists_shapiro_corestriction_map_delta_ind_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/1692ccfd-9a92-5cd6-a5c3-7ddca2e7e853
-- title:
--   Shapiro map compatible with corestriction and connecting maps
-- statement:
--   Let $G$ be a finite group, $H \le G$ a subgroup, and let $T_0$ be a short complex of $\mathbb{Z}$-linear representations of $H$ which is short exact (`hT₀`), and whose image under the induction functor `Rep.indFunctor ℤ H.subtype` is again short exact as a short complex of representations of $G$ (`hT`); let $C$ be a $\mathbb{Z}$-linear representation of $G$. The assertion is that there exist additive maps $\mathrm{Sh} \colon H^1(H, (T_0)_3) \to H^1(G, \operatorname{Ind}(T_0)_3)$ and $\mathrm{cor} \colon H^2(H, \operatorname{Res}_H C) \to H^2(G, C)$ with the following two properties. First, the composite of $\mathrm{cor}$ with the restriction map `groupCohomology.map H.subtype (𝟙 _) 2` is multiplication by the index $[G:H]$ on $H^2(G,C)$. Second, for every morphism $\varphi \colon \operatorname{Ind}(T_0)_1 \to C$ of representations of $G$ and every $y_0 \in H^1(H,(T_0)_3)$, the pushforward along $\varphi$ of $\delta(\mathrm{Sh}\,y_0) \in H^2(G,\operatorname{Ind}(T_0)_1)$ equals $\mathrm{cor}$ applied to the pushforward along the adjoint $\varphi^\flat \colon (T_0)_1 \to \operatorname{Res}_H C$ of $\varphi$ under the induction–restriction adjunction `Rep.indResAdjunction` of $\delta(y_0) \in H^2(H,(T_0)_1)$; here the two connecting maps are those of `hT` and of `hT₀` in degrees $1 \to 2$. Nothing is claimed about $\mathrm{Sh}$ beyond this compatibility; in particular it is not asserted to be an isomorphism.
--
--   This packages Shapiro's lemma for induction together with the compatibility of corestriction with connecting homomorphisms and with pushforward along a morphism of coefficients, in the single degree-one to degree-two case needed later. It is used in the Herbrand-quotient/idèle-class-group step [`M4aHerbrand.exists_level_forall_relationHom_sIdeleClassGroup_extends_or_map_delta_ne_zero`](thm.html#M4aHerbrand.exists_level_forall_relationHom_sIdeleClassGroup_extends_or_map_delta_ne_zero), where a degree-two class is transported from a subgroup to the whole group.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_exists_shapiro_corestriction_map_delta_ind_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory

theorem Rep.exists_shapiro_corestriction_map_delta_ind_eq
    {G : Type} [Group G] [Fintype G] (H : Subgroup G)
    {T₀ : ShortComplex (Rep ℤ ↥H)} (hT₀ : T₀.ShortExact)
    (hT : (T₀.map (Rep.indFunctor ℤ H.subtype)).ShortExact) (C : Rep ℤ G) :
    ∃ (Sh : groupCohomology T₀.X₃ 1 →+ groupCohomology ((Rep.indFunctor ℤ H.subtype).obj T₀.X₃) 1)
      (cor : groupCohomology (Rep.res H.subtype C) 2 →+ groupCohomology C 2),
      (∀ x : groupCohomology C 2,
        cor ((groupCohomology.map H.subtype (𝟙 (Rep.res H.subtype C)) 2).hom x) = H.index • x) ∧
      ∀ (φ : (Rep.indFunctor ℤ H.subtype).obj T₀.X₁ ⟶ C) (y₀ : groupCohomology T₀.X₃ 1),
        (groupCohomology.map (MonoidHom.id G) φ 2).hom ((groupCohomology.δ hT 1 2 rfl).hom (Sh y₀)) =
          cor ((groupCohomology.map (MonoidHom.id ↥H) ((Rep.indResAdjunction ℤ H.subtype).homEquiv T₀.X₁ C φ) 2).hom
            ((groupCohomology.δ hT₀ 1 2 rfl).hom y₀)) := by sorry
