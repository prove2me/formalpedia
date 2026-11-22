-- Prove2me | Theorems.Thm_TopGroupoid_TopologicalGroupoid_isClosed_composable_and_compactlyGenerated_eq_induced
-- name    : TopGroupoid.TopologicalGroupoid.isClosed_composable_and_compactlyGenerated_eq_induced
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T15:32:32.598803+00:00
-- url     : https://prove2.me/theorems/f73db363-6be6-47e9-83cc-e10657cf057b
-- title:
--   The composable pairs of a topological groupoid form a closed subspace of $R\times R=k(R\times_0R)$, and this subspace is the fibre product $R\times_{s,X,t}R$ of $\mathbf{CGWH}$
-- statement:
--   For a topological groupoid, the set of composable pairs of morphisms is closed in the product $R\times R$ of compactly generated weakly Hausdorff spaces, and as a subspace of it is the fibre product $R\times_{s,X,t}R$ of $\mathbf{CGWH}$.
--
--   Conventions. A topological space is *compactly generated* if its topology is coinduced by all continuous maps from compact Hausdorff spaces (no separation axiom), and *weakly Hausdorff* if the image of every continuous map from a compact Hausdorff space is closed. For a topological space $Y$, $k(Y)$ is its $k$-ification: the set $Y$ with the topology coinduced by all continuous maps from compact Hausdorff spaces to $Y$. For topological spaces $Y,Z$ we write $Y\times_0Z$ for the product with the product topology and $Y\times Z:=k(Y\times_0Z)$, which is the product in the category $\mathbf{CGWH}$ of compactly generated weakly Hausdorff spaces when $Y,Z$ are objects of it. A *topological groupoid* $(X,R,s,t,c,e,i)$ is a groupoid in sets (objects $X$, morphisms $R$, source $s$, target $t$, composition $c(g,h)$ defined when $s(g)=t(h)$, unit section $e$, inversion $i$) in which $X$ and $R$ are compactly generated weakly Hausdorff spaces, $s,t,e,i$ are continuous, and $c$ is continuous on the fibre product $R\times_{s,X,t}R$ of $\mathbf{CGWH}$, i.e. on the set $\{(g,h):s(g)=t(h)\}$ with the $k$-ification of the topology induced by $R\times_0R$.
--
--   **Statement.** Let $(X,R,s,t,c,e,i)$ be a topological groupoid and let $$P:=\{(g,h)\in R\times R:\ s(g)=t(h)\}$$ be its set of composable pairs. Then:
--
--   1. $P$ is closed in $R\times R=k(R\times_0R)$;
--   2. the $k$-ification of the topology induced on $P$ by the product topology $R\times_0R$ (the topology of the fibre product of $\mathbf{CGWH}$) coincides with the topology induced on $P$ by $R\times R=k(R\times_0R)$;
--   3. $P$, with the topology induced by $R\times R$, is compactly generated and weakly Hausdorff.
--
--   In the paper's notation: the topological fibre product $R\times^0_{s,X,t}R$ is closed as a subspace of $R\times R$, hence belongs to $\mathbf{CGWH}$, and coincides with $R\times_{s,X,t}R$. This is the special case for $s,t:R\rightrightarrows X$ of the description of fibre products in $\mathbf{CGWH}$; it identifies the domain of the composition law of a topological groupoid with a closed subspace of $R\times R$. For the product topology $R\times_0R$ the set $P$ need not be closed when $X$ is not Hausdorff: if $R=X$ and all structure maps are the identity, $P$ is the diagonal of $X$.
--
--   **Formalization Note.** `TopGroupoid.TopologicalGroupoid X R` is the structure of the definition file `TopGroupoid_TopologicalGroupoid` (for `X R : Type u` with topologies); it extends `TopGroupoid.SetGroupoid X R` and contains, as fields, the facts that `X` and `R` are compactly generated (Mathlib's `CompactlyGeneratedSpace`) and weakly Hausdorff (`CGWH.WeaklyHausdorffSpace` of the definition file `CGWH_WeakHausdorff`). `TopologicalSpace.compactlyGenerated.{u} Y` is Mathlib's $k$-ification of the topology of `Y`, with test spaces the compact Hausdorff spaces of `Type u`. Part 1 is `IsClosed[k (R × R)]` of the set `{p : R × R | G.src p.1 = G.tgt p.2}`; part 2 is an equality of two topologies on the subtype `{p : R × R // G.src p.1 = G.tgt p.2}`: the `k`-ification of its instance (subspace of the product) topology and `TopologicalSpace.induced Subtype.val (k (R × R))`; part 3 states `CompactlyGeneratedSpace` and `CGWH.WeaklyHausdorffSpace` for the latter topology, passed explicitly with `@`.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 887, Lemma E.4.2.6

import Definitions.Def_TopGroupoid_TopologicalGroupoid

open Topology TopologicalSpace

set_option autoImplicit false

universe u

namespace TopGroupoid

theorem TopologicalGroupoid.isClosed_composable_and_compactlyGenerated_eq_induced
    {X R : Type u} [TopologicalSpace X] [TopologicalSpace R] (G : TopologicalGroupoid X R) :
    IsClosed[TopologicalSpace.compactlyGenerated.{u} (R × R)]
        {p : R × R | G.src p.1 = G.tgt p.2} ∧
      TopologicalSpace.compactlyGenerated.{u} {p : R × R // G.src p.1 = G.tgt p.2} =
        TopologicalSpace.induced Subtype.val (TopologicalSpace.compactlyGenerated.{u} (R × R)) ∧
      @CompactlyGeneratedSpace {p : R × R // G.src p.1 = G.tgt p.2}
        (TopologicalSpace.induced Subtype.val (TopologicalSpace.compactlyGenerated.{u} (R × R))) ∧
      @CGWH.WeaklyHausdorffSpace {p : R × R // G.src p.1 = G.tgt p.2}
        (TopologicalSpace.induced Subtype.val
          (TopologicalSpace.compactlyGenerated.{u} (R × R))) := by sorry

end TopGroupoid
