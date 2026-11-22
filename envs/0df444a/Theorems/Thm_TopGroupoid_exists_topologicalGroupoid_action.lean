-- Prove2me | Theorems.Thm_TopGroupoid_exists_topologicalGroupoid_action
-- name    : TopGroupoid.exists_topologicalGroupoid_action
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T15:32:44.275659+00:00
-- url     : https://prove2.me/theorems/01bb7760-2678-4a21-8173-cc81ebe14508
-- title:
--   The action groupoid $G\times X\rightrightarrows X$ of a continuous action of a compactly generated weakly Hausdorff topological group is a topological groupoid
-- statement:
--   The action groupoid of a continuous group action in the category of compactly generated weakly Hausdorff spaces is a topological groupoid.
--
--   Conventions. A topological space is *compactly generated* if its topology is coinduced by all continuous maps from compact Hausdorff spaces (no separation axiom), and *weakly Hausdorff* if the image of every continuous map from a compact Hausdorff space is closed. For a topological space $Y$, $k(Y)$ is its $k$-ification: the set $Y$ with the topology coinduced by all continuous maps from compact Hausdorff spaces to $Y$. For topological spaces $Y,Z$ we write $Y\times_0Z$ for the product with the product topology and $Y\times Z:=k(Y\times_0Z)$, which is the product in the category $\mathbf{CGWH}$ of compactly generated weakly Hausdorff spaces when $Y,Z$ are objects of it. A *topological groupoid* $(X,R,s,t,c,e,i)$ is a groupoid in sets (objects $X$, morphisms $R$, source $s$, target $t$, composition $c(g,h)$ defined when $s(g)=t(h)$, unit section $e$, inversion $i$) in which $X$ and $R$ are compactly generated weakly Hausdorff spaces, $s,t,e,i$ are continuous, and $c$ is continuous on the fibre product $R\times_{s,X,t}R$ of $\mathbf{CGWH}$, i.e. on the set $\{(g,h):s(g)=t(h)\}$ with the $k$-ification of the topology induced by $R\times_0R$.
--
--   **Setting.** Let $G$ be a compactly generated weakly Hausdorff topological group: a group with a compactly generated weakly Hausdorff topology such that the inversion $G\to G$ is continuous and the multiplication is continuous as a map $G\times G=k(G\times_0G)\to G$ (this holds in particular when $G$ is a topological group in the usual sense). Let $X$ be a compactly generated weakly Hausdorff space on which $G$ acts, the action map $$a:G\times X=k(G\times_0X)\to X,\qquad a(g,x)=g\cdot x,$$ being continuous (a morphism of $\mathbf{CGWH}$).
--
--   **Statement.** The following datum $(X,R,s,t,c,e,i)$ is a topological groupoid, the *action groupoid* $G\times X\rightrightarrows X$: the space of morphisms is $R:=G\times X=k(G\times_0X)$, and $$s(g,x)=x,\qquad t(g,x)=g\cdot x,\qquad e(x)=(1,x),\qquad i(g,x)=(g^{-1},g\cdot x),$$ $$c\big((g,x),(g',x')\big)=(gg',x')\qquad\text{whenever }x=g'\cdot x'.$$
--
--   In particular $R$ is compactly generated and weakly Hausdorff, the structure maps are continuous (the composition on the fibre product of $\mathbf{CGWH}$) and the groupoid axioms hold. The stacks of the paper's Appendix E are quotient stacks associated to explicit topological groupoids, and action groupoids are the basic examples. For $X$ a point the statement shows that every compactly generated weakly Hausdorff topological group is a topological groupoid with one object.
--
--   **Formalization Note.** `TopGroupoid.TopologicalGroupoid X R` is the structure of the definition file `TopGroupoid_TopologicalGroupoid` (for `X R : Type u` with topologies); it extends `TopGroupoid.SetGroupoid X R` and contains, as fields, the facts that `X` and `R` are compactly generated (Mathlib's `CompactlyGeneratedSpace`) and weakly Hausdorff (`CGWH.WeaklyHausdorffSpace` of the definition file `CGWH_WeakHausdorff`). `TopologicalSpace.compactlyGenerated.{u} Y` is Mathlib's $k$-ification of the topology of `Y`, with test spaces the compact Hausdorff spaces of `Type u`. The hypotheses `hmul` and `hact` are continuity for the `k`-ified product topologies `TopologicalSpace.compactlyGenerated.{u} (G × G)` and `TopologicalSpace.compactlyGenerated.{u} (G × X)`; the action is a Mathlib `MulAction G X`. The conclusion is the existence of a term of `TopologicalGroupoid X (G × X)`, where the type `G × X` is given the topology `TopologicalSpace.compactlyGenerated.{u} (G × X)` (passed explicitly with `@`), whose structure maps are given by the displayed formulas; composability of `(p, q)` is `𝒢.src p = 𝒢.tgt q`, i.e. `p.2 = q.1 • q.2`. In formula (E.4.2.7) of the paper the arguments of $c$ are printed once as $((g,x),(g',x'))$ and once as $((x,g),(x',g'))$; the first form is used.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, pp. 888-889, Section E.4.2.2, (E.4.2.4) and Construction E.4.2.12

import Definitions.Def_TopGroupoid_TopologicalGroupoid

open Topology TopologicalSpace

set_option autoImplicit false

universe u

namespace TopGroupoid

theorem exists_topologicalGroupoid_action
    {G X : Type u} [Group G] [TopologicalSpace G] [CompactlyGeneratedSpace G]
    [CGWH.WeaklyHausdorffSpace G] [TopologicalSpace X] [CompactlyGeneratedSpace X]
    [CGWH.WeaklyHausdorffSpace X] [MulAction G X]
    (hmul : Continuous[TopologicalSpace.compactlyGenerated.{u} (G × G), _]
      (fun p : G × G => p.1 * p.2))
    (hinv : Continuous (fun g : G => g⁻¹))
    (hact : Continuous[TopologicalSpace.compactlyGenerated.{u} (G × X), _]
      (fun p : G × X => p.1 • p.2)) :
    ∃ 𝒢 : @TopologicalGroupoid X (G × X) _ (TopologicalSpace.compactlyGenerated.{u} (G × X)),
      (∀ p : G × X, 𝒢.src p = p.2) ∧
      (∀ p : G × X, 𝒢.tgt p = p.1 • p.2) ∧
      (∀ x : X, 𝒢.unit x = (1, x)) ∧
      (∀ p : G × X, 𝒢.inv p = (p.1⁻¹, p.1 • p.2)) ∧
      ∀ (p q : G × X) (h : 𝒢.src p = 𝒢.tgt q), 𝒢.comp ⟨(p, q), h⟩ = (p.1 * q.1, q.2) := by sorry

end TopGroupoid
