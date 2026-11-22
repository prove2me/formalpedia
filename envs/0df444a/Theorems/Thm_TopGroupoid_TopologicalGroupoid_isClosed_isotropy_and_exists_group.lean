-- Prove2me | Theorems.Thm_TopGroupoid_TopologicalGroupoid_isClosed_isotropy_and_exists_group
-- name    : TopGroupoid.TopologicalGroupoid.isClosed_isotropy_and_exists_group
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T15:32:36.02665+00:00
-- url     : https://prove2.me/theorems/5e62ffb9-2857-4d37-9289-fb3c5668b61f
-- title:
--   The isotropy group $R_x=s^{-1}(x)\cap t^{-1}(x)$ of a topological groupoid is closed in $R$ and is a compactly generated weakly Hausdorff topological group
-- statement:
--   The isotropy groups of a topological groupoid are closed in the space of morphisms and are group objects of the category of compactly generated weakly Hausdorff spaces.
--
--   Conventions. A topological space is *compactly generated* if its topology is coinduced by all continuous maps from compact Hausdorff spaces (no separation axiom), and *weakly Hausdorff* if the image of every continuous map from a compact Hausdorff space is closed. For a topological space $Y$, $k(Y)$ is its $k$-ification: the set $Y$ with the topology coinduced by all continuous maps from compact Hausdorff spaces to $Y$. For topological spaces $Y,Z$ we write $Y\times_0Z$ for the product with the product topology and $Y\times Z:=k(Y\times_0Z)$, which is the product in the category $\mathbf{CGWH}$ of compactly generated weakly Hausdorff spaces when $Y,Z$ are objects of it. A *topological groupoid* $(X,R,s,t,c,e,i)$ is a groupoid in sets (objects $X$, morphisms $R$, source $s$, target $t$, composition $c(g,h)$ defined when $s(g)=t(h)$, unit section $e$, inversion $i$) in which $X$ and $R$ are compactly generated weakly Hausdorff spaces, $s,t,e,i$ are continuous, and $c$ is continuous on the fibre product $R\times_{s,X,t}R$ of $\mathbf{CGWH}$, i.e. on the set $\{(g,h):s(g)=t(h)\}$ with the $k$-ification of the topology induced by $R\times_0R$.
--
--   **Statement.** Let $(X,R,s,t,c,e,i)$ be a topological groupoid and let $x\in X$. Consider the subspace $$R_x:=s^{-1}(x)\cap t^{-1}(x)\subseteq R$$ of the morphisms from $x$ to $x$. Then:
--
--   1. $R_x$ is closed in $R$;
--   2. $R_x$, with the subspace topology, is compactly generated and weakly Hausdorff;
--   3. $R_x$ is a group for the multiplication $g\cdot h:=c(g,h)$, with unit $e(x)$ and inverse $g^{-1}=i(g)$; the inversion $R_x\to R_x$ is continuous and the multiplication is continuous as a map $R_x\times R_x=k(R_x\times_0R_x)\to R_x$.
--
--   So $R_x$ is a compactly generated weakly Hausdorff topological group, in the sense of a group object of $\mathbf{CGWH}$. For the action groupoid $G\times X\rightrightarrows X$ of a group action, $R_x$ is the set of pairs $(g,x)$ with $g\cdot x=x$, a copy of the stabilizer of $x$.
--
--   **Formalization Note.** `TopGroupoid.TopologicalGroupoid X R` is the structure of the definition file `TopGroupoid_TopologicalGroupoid` (for `X R : Type u` with topologies); it extends `TopGroupoid.SetGroupoid X R` and contains, as fields, the facts that `X` and `R` are compactly generated (Mathlib's `CompactlyGeneratedSpace`) and weakly Hausdorff (`CGWH.WeaklyHausdorffSpace` of the definition file `CGWH_WeakHausdorff`). `TopologicalSpace.compactlyGenerated.{u} Y` is Mathlib's $k$-ification of the topology of `Y`, with test spaces the compact Hausdorff spaces of `Type u`. `G.isotropy x` is the set `{g : R | G.src g = x ∧ G.tgt g = x}` of the definition file, coerced to a subtype with its subspace topology. The group structure is asserted existentially (`∃ _ : Group (G.isotropy x)`) and pinned down by the three identities for `*`, `1` and `⁻¹`. The continuity of the multiplication is stated for the `k`-ification `TopologicalSpace.compactlyGenerated.{u}` of the product topology of `G.isotropy x × G.isotropy x`, i.e. for the product of $\mathbf{CGWH}$, which is what "topological group" means for the paper's product $\times$ and what the continuity of $c$ on the fibre product of $\mathbf{CGWH}$ gives; continuity for the product topology $R_x\times_0R_x$ (Mathlib's `IsTopologicalGroup`) is not asserted.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 887, Lemma E.4.2.7

import Definitions.Def_TopGroupoid_TopologicalGroupoid

open Topology TopologicalSpace

set_option autoImplicit false

universe u

namespace TopGroupoid

theorem TopologicalGroupoid.isClosed_isotropy_and_exists_group
    {X R : Type u} [TopologicalSpace X] [TopologicalSpace R] (G : TopologicalGroupoid X R) (x : X) :
    IsClosed (G.isotropy x) ∧
      CompactlyGeneratedSpace (G.isotropy x) ∧
      CGWH.WeaklyHausdorffSpace (G.isotropy x) ∧
      ∃ _ : Group (G.isotropy x),
        (∀ g h : G.isotropy x,
          ((g * h : G.isotropy x) : R) = G.comp ⟨((g : R), (h : R)), g.2.1.trans h.2.2.symm⟩) ∧
        ((1 : G.isotropy x) : R) = G.unit x ∧
        (∀ g : G.isotropy x, ((g⁻¹ : G.isotropy x) : R) = G.inv g) ∧
        Continuous (fun g : G.isotropy x => g⁻¹) ∧
        Continuous[TopologicalSpace.compactlyGenerated.{u} (G.isotropy x × G.isotropy x), _]
          (fun p : G.isotropy x × G.isotropy x => p.1 * p.2) := by sorry

end TopGroupoid
