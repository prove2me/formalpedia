-- Prove2me | Theorems.Thm_TwinWidthI_FOInterp_lemma_7_13
-- name    : TwinWidthI.FOInterp.lemma_7_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:45:12.929966+00:00
-- url     : https://prove2.me/theorems/fa4f1e36-d3c0-4148-aa7b-dad4cfa7b649
-- title:
--   Lemma 7.13 — the pruned ℓ-shuffle of all MT_ℓ(G, P, X) is exactly MT_ℓ(G, P)
-- statement:
--   Let $\ell>0$ and let $(G,\mathcal P)$ be a partitioned finite simple graph. Then the pruned $\ell$-shuffle of the trees $MT_\ell(G,\mathcal P,X)$, where $X$ ranges over the parts of $\mathcal P$, is exactly the complete tree:
--   $$\operatorname{pruned-shuffle}_\ell\bigl(MT_\ell(G,\mathcal P,X)\bigr)_{X\in\mathcal P}=MT_\ell(G,\mathcal P).$$
--
--   Every tuple of length at most $\ell$ splits into the subtuples of the components of its sequence graph, each a connected tuple rooted at its own local root. With Lemma 7.12 this gives Lemma 7.14.
--
--   **Formalization Note.** Both sides are sets of tuples; $MT_\ell(G,\mathcal P)$ is the set of all tuples of length at most $\ell$. The standing assumption $\ell>0$ of §7.3 is a hypothesis.
-- source:
--   Bonnet, Kim, Thomassé and Watrigant, Twin-width I: Tractable FO Model Checking, J. ACM 69(1), Article 3 (2021), p. 3:38, Lemma 7.13 (standing assumption ℓ > 0 of §7.3, p. 3:35)

import Mathlib
import Definitions.Def_TwinWidthI_FOInterp_Setting
import Definitions.Def_TwinWidthI_FOInterp_MorphismTree

namespace TwinWidthI.FOInterp

open Finset

theorem lemma_7_13 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (P : Finpartition (univ : Finset V)) (ℓ : ℕ) (hℓ : 0 < ℓ) :
    prunedShuffle G P ℓ (MTX G P ℓ) = MT V ℓ := by sorry

end TwinWidthI.FOInterp
