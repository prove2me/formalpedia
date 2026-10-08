-- Prove2me | Theorems.Thm_TwinWidthI_FOInterp_lemma_7_11
-- name    : TwinWidthI.FOInterp.lemma_7_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:44:56.236811+00:00
-- url     : https://prove2.me/theorems/0c19dda2-038c-41d8-8251-17ecc84f2ad4
-- title:
--   Lemma 7.11 — restricting to connected tuples rooted at X commutes with reductions
-- statement:
--   Let $\ell>0$, let $G$ be a finite simple graph with a partition $\mathcal P$, let $T$ be a morphism-tree in $(G,\mathcal P)$ with all nodes of length at most $\ell$, and let $X$ be a part of $\mathcal P$. For every reduction $T^r$ of $T$ in $(G,\mathcal P)$,
--   $$T^r_X\ \text{is a reduction of}\ T_X\ \text{in}\ (G,\mathcal P),$$
--   where $T_X$ denotes the root together with the nodes of $T$ that are connected tuples rooted at $X$.
--
--   Together with Lemma 7.12 this lets reductions be computed part by part; it is used in the proof of Lemma 8.6.
--
--   **Formalization Note.** A morphism-tree is a prefix-closed set of tuples containing the empty tuple. The paper's trees in §7.3 are $\ell$-morphism-trees for the fixed $\ell>0$ of the section ("Let $\ell>0$ be some fixed integer", p. 3:35); both are hypotheses here.
-- source:
--   Bonnet, Kim, Thomassé and Watrigant, Twin-width I: Tractable FO Model Checking, J. ACM 69(1), Article 3 (2021), p. 3:35, Lemma 7.11 (standing assumption ℓ > 0 of §7.3, p. 3:35)

import Mathlib
import Definitions.Def_TwinWidthI_FOInterp_Setting
import Definitions.Def_TwinWidthI_FOInterp_MorphismTree

namespace TwinWidthI.FOInterp

open Finset

theorem lemma_7_11 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (P : Finpartition (univ : Finset V)) (ℓ : ℕ) (hℓ : 0 < ℓ) (T Tr : Set (List V))
    (hT : IsTupleTree T) (hTℓ : T ⊆ MT V ℓ) (X : Finset V) (hX : X ∈ P.parts)
    (hTr : IsReduction G P T Tr) :
    IsReduction G P (restrictTo G P ℓ T X) (restrictTo G P ℓ Tr X) := by sorry

end TwinWidthI.FOInterp
