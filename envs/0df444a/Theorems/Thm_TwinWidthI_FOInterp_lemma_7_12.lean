-- Prove2me | Theorems.Thm_TwinWidthI_FOInterp_lemma_7_12
-- name    : TwinWidthI.FOInterp.lemma_7_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:45:05.794214+00:00
-- url     : https://prove2.me/theorems/8b2c6945-16ce-4d9f-aac9-a0dc5a7d5d1e
-- title:
--   Lemma 7.12 — the pruned shuffle commutes with reductions
-- statement:
--   Let $\ell>0$, let $G$ be a finite simple graph with a partition $\mathcal P$, and for every part $X$ of $\mathcal P$ let $T_X$ be a morphism-tree in $(G,\mathcal P,X)$ (its non-root nodes are connected tuples rooted at $X$ of length at most $\ell$). Fix a part $X_1$ and a reduction $T^r_{X_1}$ of $T_{X_1}$ in $(G,\mathcal P)$. Then the pruned $\ell$-shuffle of the family obtained by replacing $T_{X_1}$ with $T^r_{X_1}$ is a reduction, in $(G,\mathcal P)$, of the pruned $\ell$-shuffle of the family $(T_X)_X$.
--
--   The paper calls this "the cornerstone of the whole section": it allows the reduct of $MT_\ell(G,\mathcal P)$ to be assembled from reducts of the local trees, and it is used in Lemmas 7.14, 8.5 and 8.6.
--
--   **Formalization Note.** The paper states the lemma for distinct parts $X_1,\dots,X_p$ with one tree each; here the family is indexed by all parts, which covers the paper's case by taking the one-node tree $\{\varepsilon\}$ for the remaining parts. The pruned shuffle is the characterisation given in the definition item.
-- source:
--   Bonnet, Kim, Thomassé and Watrigant, Twin-width I: Tractable FO Model Checking, J. ACM 69(1), Article 3 (2021), p. 3:36, Lemma 7.12 (notation of p. 3:36, standing assumption ℓ > 0 of §7.3, p. 3:35)

import Mathlib
import Definitions.Def_TwinWidthI_FOInterp_Setting
import Definitions.Def_TwinWidthI_FOInterp_MorphismTree

namespace TwinWidthI.FOInterp

open Finset

theorem lemma_7_12 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (P : Finpartition (univ : Finset V)) (ℓ : ℕ) (hℓ : 0 < ℓ) (F : Finset V → Set (List V))
    (hF : ∀ X ∈ P.parts, IsTreeIn G P ℓ X (F X)) (X₁ : Finset V) (hX₁ : X₁ ∈ P.parts)
    (T₁r : Set (List V)) (hr : IsReduction G P (F X₁) T₁r) :
    IsReduction G P (prunedShuffle G P ℓ F)
      (prunedShuffle G P ℓ (Function.update F X₁ T₁r)) := by sorry

end TwinWidthI.FOInterp
