-- Prove2me | Theorems.Thm_TwinWidthI_FOInterp_lemma_7_3
-- name    : TwinWidthI.FOInterp.lemma_7_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:44:56.810522+00:00
-- url     : https://prove2.me/theorems/e9658f25-a5ed-4106-8979-11241999a59d
-- title:
--   Lemma 7.3 — any reduct of an ℓ-morphism-tree has size at most h(ℓ)
-- statement:
--   For every integer $\ell\ge 0$ there is an integer $H(\ell)$ such that the following holds. Let $G$ be any finite simple graph and let $T$ be a reduct, in $G$, of the complete $\ell$-morphism-tree $MT_\ell(G)$; that is, $T$ is obtained from $MT_\ell(G)$ by a sequence of reductions deleting one of two equivalent siblings with its descendants, and no two siblings of $T$ are equivalent. Then
--   $$|T|\le H(\ell).$$
--
--   The bound does not depend on $G$ or on its number of vertices, although $MT_\ell(G)$ itself has $n^\ell+n^{\ell-1}+\dots+1$ nodes. This is what makes reducts usable as bounded-size certificates for all prenex formulas of depth at most $\ell$; its analogue for partitioned graphs bounds the reducts in the proof of Lemma 8.5.
--
--   **Formalization Note.** Morphism-trees are sets of tuples (see the definition item); "in $G$" means that automorphisms are taken with respect to the one-part partition $\top$, which imposes no condition. "Size" is the number of nodes, the root included. The bound $H$ is chosen before the graph.
-- source:
--   Bonnet, Kim, Thomassé and Watrigant, Twin-width I: Tractable FO Model Checking, J. ACM 69(1), Article 3 (2021), p. 3:32, Lemma 7.3

import Mathlib
import Definitions.Def_TwinWidthI_FOInterp_Setting
import Definitions.Def_TwinWidthI_FOInterp_MorphismTree

namespace TwinWidthI.FOInterp

open Finset

theorem lemma_7_3 (ℓ : ℕ) :
    ∃ H : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) (T : Set (List V)),
      IsReduct G ⊤ (MT V ℓ) T → T.ncard ≤ H := by sorry

end TwinWidthI.FOInterp
