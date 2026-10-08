-- Prove2me | Theorems.Thm_ThompsonAmenability_isAmenable_of_isExtensivelyAmenableOn_of_cocycle
-- name    : ThompsonAmenability.isAmenable_of_isExtensivelyAmenableOn_of_cocycle
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-06T10:59:54.064059+00:00
-- url     : https://prove2.me/theorems/dd4dc306-5e82-47e1-8ed8-724ca46e62c8
-- title:
--   Juschenko–Matte Bon–Monod–de la Salle, Corollary 1.4, case of a free affine action — an extensively amenable action carrying a free affine cocycle action makes the group amenable
-- statement:
--   Let a group $G$ act on a set $X$, let $L$ be an abelian group, and let $c : G \to L^{(X)}$ be a map into the finitely supported functions $X \to L$ (`X →₀ L`) such that
--
--   - every $c(g)$ is supported in a set $Y \subseteq X$;
--   - $c(gh) = c(g) + g_* c(h)$ for all $g, h \in G$, where $g_*\varphi$ is the push-forward of $\varphi$ along $x \mapsto g \cdot x$ (`Finsupp.mapDomain (g • ·)`);
--   - the affine action $\varphi \mapsto c(g) + g_*\varphi$ of $G$ on $L^{(X)}$ is free: $c(g) + g_*\varphi = \varphi$ only when $g = 1$.
--
--   If the action of $G$ on $X$ is extensively amenable relative to $Y$ (`IsExtensivelyAmenableOn G X Y`), then $G$ is amenable (`Garrido.IsAmenable G`).
--
--   Juschenko, Matte Bon, Monod and de la Salle, p. 3: “Corollary 1.4. Let $G \curvearrowright X$ be an extensively amenable action and let $F : \mathbf I \to \mathbf{Amen}$ be any functor. A subgroup $H$ of $F(X) \rtimes G$ is amenable as soon as the intersection $H \cap (\{1\} \times G)$ is so.” and “Remark 1.5. A particular case in which this criterion applies is when one is able to construct a twisted embedding $G \hookrightarrow F(X) \ltimes G$ of the form $g \mapsto (c_g, g)$ with the property that $\{g \in G : c_g = 1\}$ is an amenable subgroup of $G$. We then say that $c : G \to F(X)$, $g \mapsto c_g$ is a $F(X)$-cocycle with amenable kernel. The conclusion is then that $G$ is amenable.”
--
--   **Formalization note.** This is the case of Remark 1.5 for the functor $X \mapsto L^{(X)}$, under a stronger hypothesis: every point stabilizer of the affine action is trivial, not only the kernel $\{g : c(g) = 0\}$ amenable. Extensive amenability is taken relative to a set $Y$ containing the supports of the cocycle, as in the bundle's `IsExtensivelyAmenableOn`.
-- source:
--   Standalone theorem: the case of Juschenko, K., Matte Bon, N., Monod, N. and de la Salle, M., Extensive amenability and an application to interval exchanges, Ergodic Theory Dynam. Systems 38 (2018) 195–219, https://doi.org/10.1017/etds.2016.32 (arXiv:1503.04977v1, whose page numbers are used), p. 3, Corollary 1.4 and Remark 1.5, for a cocycle into the finitely supported functions with values in an abelian group whose affine action is free

import Definitions.Def_Garrido_Amenability
import Definitions.Def_ThompsonAmenability
import Mathlib

namespace ThompsonAmenability

theorem isAmenable_of_isExtensivelyAmenableOn_of_cocycle {G X L : Type*} [Group G] [MulAction G X]
    [AddCommGroup L] (Y : Set X) (c : G → X →₀ L)
    (hsupp : ∀ g, (↑(c g).support : Set X) ⊆ Y)
    (hmul : ∀ g h, c (g * h) = c g + Finsupp.mapDomain (fun x => g • x) (c h))
    (hfree : ∀ (g : G) (φ : X →₀ L), c g + Finsupp.mapDomain (fun x => g • x) φ = φ → g = 1)
    (hY : IsExtensivelyAmenableOn G X Y) : Garrido.IsAmenable G := by
  sorry

end ThompsonAmenability
