-- Prove2me | Theorems.Thm_Rep_shortExact_map_resFunctor
-- name    : Rep.shortExact_map_resFunctor
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/1f7068da-9c9f-53e3-99bf-0fff6b31bbd8
-- title:
--   Restriction along a group homomorphism is exact on Rep
-- statement:
--   Let $k$ be a commutative ring, let $G$ and $H$ be groups, and let $f \colon H \to G$ be a group homomorphism. Let $X$ be a short complex in the category $\mathrm{Rep}\,k\,G$ of $k$-linear representations of $G$, that is, a pair of composable morphisms $X_1 \xrightarrow{f} X_2 \xrightarrow{g} X_3$ with zero composite, and assume $X$ is short exact: $X_1 \to X_2$ is a monomorphism, $X_2 \to X_3$ is an epimorphism, and the complex is exact at $X_2$. The assertion is that the short complex obtained by applying the restriction functor `Rep.resFunctor f` from $\mathrm{Rep}\,k\,G$ to $\mathrm{Rep}\,k\,H$ termwise to $X$ is again short exact, i.e. the restricted morphism $\mathrm{Res}_f X_1 \to \mathrm{Res}_f X_2$ is a monomorphism, $\mathrm{Res}_f X_2 \to \mathrm{Res}_f X_3$ is an epimorphism, and the restricted complex is exact in the middle. No hypothesis is imposed on $f$; in particular it need not be injective, so this covers restriction along arbitrary homomorphisms and not only along inclusions of subgroups.
--
--   This is the exactness of the restriction functor on categories of linear representations, the statement that $\mathrm{Res}_f$ carries short exact sequences to short exact sequences. It is used to restrict dimension-shifting and free-resolution sequences from $G$ to $H$, and is cited in the construction of Tate cohomology arguments, for instance [`Rep.exists_shortExact_free_of_forall_isZero`](thm.html#Rep.exists_shortExact_free_of_forall_isZero), [`Rep.isZero_tateCohomology_res_splittingModule`](thm.html#Rep.isZero_tateCohomology_res_splittingModule) and [`Rep.IsTateCupProduct.bijective_cup_of_h1_h2`](thm.html#Rep.IsTateCupProduct.bijective_cup_of_h1_h2).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_shortExact_map_resFunctor.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u
open CategoryTheory Rep

theorem Rep.shortExact_map_resFunctor {k G H : Type u} [CommRing k] [Group G] [Group H] (f : H →* G)
    {X : ShortComplex (Rep.{u} k G)} (hX : X.ShortExact) :
    (X.map (Rep.resFunctor f)).ShortExact := by sorry
