-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P18_crossedModule_strictTwoGroup
-- name    : QAlgorithms.Papers.Independent.Renew46.P18.crossedModule_strictTwoGroup
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T20:19:46.981826+00:00
-- url     : https://prove2.me/theorems/f133d22a-8baf-4bac-943b-608f67bb1bd4
-- title:
--   A crossed module gives the specified strict 2-group
-- statement:
--   Let $H$ and $G$ be arbitrary groups, $\tau:H\to G$ a group homomorphism, and $\rho:G\to\operatorname{Aut}(H)$ an automorphic action. Suppose the crossed-module equations hold:
--   $$
--   \tau(\rho(g)h)=g\tau(h)g^{-1},\qquad
--   \rho(\tau(h))k=hkh^{-1}.
--   $$
--   There is a strict 2-group with object group $G$ and arrow group $H\rtimes_\rho G$. Its structure maps are
--   $$
--   s(h,g)=g,\quad t(h,g)=\tau(h)g,\quad \mathrm{id}_g=(e,g),\quad
--   (h',\tau(h)g)\circ(h,g)=(h'h,g).
--   $$
--   The unit object is $e$. Tensor product and specified tensor inversion are the group multiplication and group inverse in $G$ and $H\rtimes_\rho G$; in particular,
--   $$
--   (h,g)\otimes(k,l)=(h\,\rho(g)k,gl),\qquad
--   \overline{(h,g)}=(\rho(g^{-1})(h^{-1}),g^{-1}).
--   $$
--   Categorical arrow inversion is instead $(h,g)\mapsto(h^{-1},\tau(h)g)$. The associator is the identity. These operations satisfy the groupoid laws, functoriality of tensor and tensor inversion, strict unit and strict two-sided tensor inverse laws, and all associator coherence and normalization laws of Definition III.1.
--
--   This gives the explicit strict 2-group construction from a crossed module without imposing topology or connectedness.
-- source:
--   Categorified central extensions, \'etale Lie 2-groups and Lie's Third Theorem for locally exponential Lie algebras, arXiv:0812.1673v3, PDF p. 15, Example III.3: crossed module to strict 2-group

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P18

namespace QAlgorithms.Papers.Independent.Renew46.P18

universe u v w x

/-- Example III.3, PDF p. 15: a crossed module gives the explicitly
specified strict 2-group with objects G, arrows H semidirect G, and
identity associator. Multiplication and specified tensor inversion are
the group operations; categorical arrow inversion is a separate map. -/
theorem crossedModule_strictTwoGroup
    {H : Type u} {G : Type v} [Group H] [Group G]
    (tau : H →* G) (rho : G →* MulAut H) (h : IsCrossedModule tau rho) :
    IsStrictTwoGroup (crossedSource rho) (crossedTarget tau rho)
      (crossedIdentity rho) (crossedCompose rho) (crossedArrowInverse tau rho) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P18
