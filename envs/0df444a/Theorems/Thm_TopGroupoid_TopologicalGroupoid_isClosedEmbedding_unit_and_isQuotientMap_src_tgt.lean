-- Prove2me | Theorems.Thm_TopGroupoid_TopologicalGroupoid_isClosedEmbedding_unit_and_isQuotientMap_src_tgt
-- name    : TopGroupoid.TopologicalGroupoid.isClosedEmbedding_unit_and_isQuotientMap_src_tgt
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T15:32:33.538804+00:00
-- url     : https://prove2.me/theorems/8ddf9f6a-71a8-4fce-a970-e5edd0706c4d
-- title:
--   In a topological groupoid the unit section $e:X\to R$ is a closed embedding and the source and target maps $s,t:R\to X$ are quotient maps
-- statement:
--   The unit section of a topological groupoid is a closed embedding, and its source and target maps are quotient maps.
--
--   Conventions. A topological space is *compactly generated* if its topology is coinduced by all continuous maps from compact Hausdorff spaces (no separation axiom), and *weakly Hausdorff* if the image of every continuous map from a compact Hausdorff space is closed. For a topological space $Y$, $k(Y)$ is its $k$-ification: the set $Y$ with the topology coinduced by all continuous maps from compact Hausdorff spaces to $Y$. For topological spaces $Y,Z$ we write $Y\times_0Z$ for the product with the product topology and $Y\times Z:=k(Y\times_0Z)$, which is the product in the category $\mathbf{CGWH}$ of compactly generated weakly Hausdorff spaces when $Y,Z$ are objects of it. A *topological groupoid* $(X,R,s,t,c,e,i)$ is a groupoid in sets (objects $X$, morphisms $R$, source $s$, target $t$, composition $c(g,h)$ defined when $s(g)=t(h)$, unit section $e$, inversion $i$) in which $X$ and $R$ are compactly generated weakly Hausdorff spaces, $s,t,e,i$ are continuous, and $c$ is continuous on the fibre product $R\times_{s,X,t}R$ of $\mathbf{CGWH}$, i.e. on the set $\{(g,h):s(g)=t(h)\}$ with the $k$-ification of the topology induced by $R\times_0R$.
--
--   **Statement.** Let $(X,R,s,t,c,e,i)$ be a topological groupoid. Then:
--
--   1. the unit section $e:X\to R$ is a closed embedding (a homeomorphism onto a closed subspace of $R$);
--   2. the source map $s:R\to X$ and the target map $t:R\to X$ are quotient maps (surjective, and a subset of $X$ is open if and only if its preimage in $R$ is open).
--
--   Part 1 identifies the space of objects $X$ with the closed subspace $e(X)\subseteq R$ of identity arrows. In the paper's terminology closed embeddings are *closed immersions* and quotient maps are *submersive maps*; it is the first lemma of §E.4.2 of the paper on topological groupoids.
--
--   **Formalization Note.** `TopGroupoid.TopologicalGroupoid X R` is the structure of the definition file `TopGroupoid_TopologicalGroupoid` (for `X R : Type u` with topologies); it extends `TopGroupoid.SetGroupoid X R` and contains, as fields, the facts that `X` and `R` are compactly generated (Mathlib's `CompactlyGeneratedSpace`) and weakly Hausdorff (`CGWH.WeaklyHausdorffSpace` of the definition file `CGWH_WeakHausdorff`). `TopologicalSpace.compactlyGenerated.{u} Y` is Mathlib's $k$-ification of the topology of `Y`, with test spaces the compact Hausdorff spaces of `Type u`. `G.unit`, `G.src`, `G.tgt` are the unit section, source and target of `G`; the conclusion uses Mathlib's `IsClosedEmbedding` and `IsQuotientMap` (which includes surjectivity).
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 887, Lemma E.4.2.5

import Definitions.Def_TopGroupoid_TopologicalGroupoid

open Topology TopologicalSpace

set_option autoImplicit false

universe u

namespace TopGroupoid

theorem TopologicalGroupoid.isClosedEmbedding_unit_and_isQuotientMap_src_tgt
    {X R : Type u} [TopologicalSpace X] [TopologicalSpace R] (G : TopologicalGroupoid X R) :
    IsClosedEmbedding G.unit ∧ IsQuotientMap G.src ∧ IsQuotientMap G.tgt := by sorry

end TopGroupoid
