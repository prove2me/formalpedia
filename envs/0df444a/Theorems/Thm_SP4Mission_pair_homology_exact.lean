-- Prove2me | Theorems.Thm_SP4Mission_pair_homology_exact
-- name    : SP4Mission.pair_homology_exact
-- status  : Proved
-- author  : @ryanshin
-- created : 2026-09-12T22:20:28.659044+00:00
-- url     : https://prove2.me/theorems/7769b11e-be09-42e6-8267-2b9318b80688
-- title:
--   Long exact sequence of a pair (Hatcher, Theorem 2.16)
-- statement:
--   Let $\iota\colon V\hookrightarrow M$ be an injective continuous map (the inclusion of a subspace). Then the integral singular homology groups of $V$, $M$ and of the pair $(M,V)$ fit into a long exact sequence
--
--   $$
--   \cdots\longrightarrow H_{k+1}(M,V)\xrightarrow{\ \partial\ }H_k(V)\xrightarrow{\ \iota_*\ }H_k(M)\xrightarrow{\ j_*\ }H_k(M,V)\xrightarrow{\ \partial\ }H_{k-1}(V)\longrightarrow\cdots
--   $$
--
--   Precisely, for every $k\ge0$ the sequence is exact at $H_k(M)$ (the image of $\iota_*$ is the kernel of $j_*$), at $H_{k+1}(M,V)$ (the image of $j_*$ is the kernel of $\partial$), and at $H_k(V)$ (the image of $\partial\colon H_{k+1}(M,V)\to H_k(V)$ is the kernel of $\iota_*$). This is the long exact sequence of homology groups associated with the short exact sequence of chain complexes $0\to C_\bullet(V)\to C_\bullet(M)\to C_\bullet(M,V)\to 0$; it is the basic computational tool relating the homology of a space, a subspace and the pair, and in the mission it is used for the pair $(M, M\setminus\{p\})$ of a closed manifold and its punctured version.
--
--   **Formalization Note** Exactness is expressed by Mathlib's `ShortComplex.Exact` for the three short complexes built from `SP4Homology.map k ι` ($\iota_*$), `SP4Homology.toRel k ι` ($j_*$) and `SP4Homology.relδ k ι hι` ($\partial$); in `ModuleCat ℤ` this is the equality of the range of the first map with the kernel of the second. Mathlib's snake lemma for chain complexes (`ShortComplex.ShortExact.homology_exact₁/₂/₃`) applies to the short exact sequence `SP4Homology.relShortComplex_shortExact ι hι`.
-- source:
--   Allen Hatcher, Algebraic Topology, Cambridge University Press, 2002 (author's edition: https://pi.math.cornell.edu/~hatcher/AT/AT.pdf), §2.1, Theorem 2.16, p. 117 (the long exact sequence of homology groups of a short exact sequence of chain complexes), applied on pp. 115–118 to 0 → Cₙ(A) → Cₙ(X) → Cₙ(X, A) → 0 to obtain the long exact sequence of the pair (X, A): ··· → Hₙ(A) → Hₙ(X) → Hₙ(X, A) → Hₙ₋₁(A) → ···.

import Definitions.Def_SP4Sphere
import Definitions.Def_SP4WeakHomotopy
import Definitions.Def_SP4Homology
import Definitions.Def_SP4HomologyMap
import Definitions.Def_SP4RelHomology

set_option autoImplicit false

open scoped Manifold ContDiff
open SP4Mission CategoryTheory Limits

theorem SP4Mission.pair_homology_exact {V M : Type} [TopologicalSpace V] [TopologicalSpace M]
    (ι : C(V, M)) (hι : Function.Injective ι) (k : ℕ) :
    (ShortComplex.mk (SP4Homology.map k ι) (SP4Homology.toRel k ι)
      (SP4Homology.map_toRel k ι)).Exact ∧
    (ShortComplex.mk (SP4Homology.toRel (k + 1) ι) (SP4Homology.relδ k ι hι)
      (SP4Homology.toRel_relδ k ι hι)).Exact ∧
    (ShortComplex.mk (SP4Homology.relδ k ι hι) (SP4Homology.map k ι)
      (SP4Homology.relδ_map k ι hι)).Exact := by sorry
