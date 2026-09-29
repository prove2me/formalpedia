-- Prove2me | Theorems.Thm_Rep_exists_ind_map_comp_eq_iff_exists_comp_eq_homEquiv
-- name    : Rep.exists_ind_map_comp_eq_iff_exists_comp_eq_homEquiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/7ddf4747-129f-50ff-9f4c-ec1f15627538
-- title:
--   Extension along Ind f₀ versus extension along f₀
-- statement:
--   Let $G$ be a group and $H \le G$ a subgroup, and write $\mathrm{Ind}$ for the functor `Rep.indFunctor ℤ H.subtype` from $\mathbb{Z}$-linear representations of $H$ to $\mathbb{Z}$-linear representations of $G$ obtained by induction along the inclusion $H \hookrightarrow G$, and $\mathrm{Res}$ for the restriction functor `Rep.res H.subtype` in the opposite direction. Given objects $R_0, P_0$ of `Rep ℤ ↥H`, a morphism $f_0 : R_0 \to P_0$ of $H$-representations over $\mathbb{Z}$, an object $C$ of `Rep ℤ G`, and a morphism $\varphi : \mathrm{Ind}\,R_0 \to C$ of $G$-representations, the assertion is an equivalence of two solvability statements. The first is that there exists a morphism $\chi : \mathrm{Ind}\,P_0 \to C$ with $\mathrm{Ind}\,f_0$ followed by $\chi$ equal to $\varphi$. The second is that there exists a morphism $\chi_0 : P_0 \to \mathrm{Res}\,C$ of $H$-representations with $f_0$ followed by $\chi_0$ equal to the image of $\varphi$ under the hom-bijection of the adjunction `Rep.indResAdjunction ℤ H.subtype` at the pair $(R_0, C)$, i.e. equal to the Frobenius adjoint of $\varphi$.
--
--   This is the statement that Frobenius reciprocity for the adjunction $\mathrm{Ind} \dashv \mathrm{Res}$ between $\mathbb{Z}$-linear representations of $H$ and of $G$ is compatible with extension problems: a map out of $\mathrm{Ind}\,R_0$ extends through $\mathrm{Ind}\,f_0$ exactly when its adjoint extends through $f_0$. It is used in the Herbrand-quotient part of the development, where an extension problem over $G$ for an induced module is transferred to the corresponding extension problem over the subgroup $H$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_exists_ind_map_comp_eq_iff_exists_comp_eq_homEquiv.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory

theorem Rep.exists_ind_map_comp_eq_iff_exists_comp_eq_homEquiv
    {G : Type} [Group G] (H : Subgroup G) {R₀ P₀ : Rep ℤ ↥H} (f₀ : R₀ ⟶ P₀) (C : Rep ℤ G)
    (φ : (Rep.indFunctor ℤ H.subtype).obj R₀ ⟶ C) :
    (∃ χ : (Rep.indFunctor ℤ H.subtype).obj P₀ ⟶ C, (Rep.indFunctor ℤ H.subtype).map f₀ ≫ χ = φ) ↔
      ∃ χ₀ : P₀ ⟶ Rep.res H.subtype C, f₀ ≫ χ₀ = (Rep.indResAdjunction ℤ H.subtype).homEquiv R₀ C φ := by sorry
