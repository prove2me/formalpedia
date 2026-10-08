-- Prove2me | Theorems.Thm_TwinWidthI_FOInterp_lemma_8_5
-- name    : TwinWidthI.FOInterp.lemma_8_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:45:24.591252+00:00
-- url     : https://prove2.me/theorems/78aa4988-8a4c-41f1-834a-da06c2741737
-- title:
--   Lemma 8.5 — a part of a d-partition meets at most f(d, ℓ) components of E_{ℓ+2}(G, P)
-- statement:
--   For all integers $d,\ell\ge 0$ there is an integer $B(d,\ell)$ such that the following holds. Let $G$ be a finite simple graph, $\mathcal P$ a $d$-partition of $G$ and $X$ a part of $\mathcal P$. Then the number of connected components of $E_{\ell+2}(G,\mathcal P)$ inside $X$ is at most $B(d,\ell)$:
--   $$\bigl|\{\,C : C \text{ a component of } E_{\ell+2}(G,\mathcal P),\ C\cap X\neq\emptyset\,\}\bigr|\le B(d,\ell).$$
--
--   So $I_{\ell+2}(G,\mathcal P)$ refines the $d$-partition $\mathcal P$ only boundedly: each part of $\mathcal P$ splits into at most $B(d,\ell)$ parts. This is the bounded-refinement half of the proof of Theorem 8.3.
--
--   **Formalization Note.** Components are counted as the image of $X$ under the map sending a vertex to its connected component in `Eind G P (ℓ + 2)`. "Inside $X$" is rendered as "meeting $X$"; since $I_{\ell+2}(G,\mathcal P)$ refines $\mathcal P$, the two counts agree. $B$ is chosen before the graph and the partition.
-- source:
--   Bonnet, Kim, Thomassé and Watrigant, Twin-width I: Tractable FO Model Checking, J. ACM 69(1), Article 3 (2021), p. 3:42, Lemma 8.5

import Mathlib
import Definitions.Def_TwinWidthI_FOInterp_Setting
import Definitions.Def_TwinWidthI_FOInterp_MorphismTree

namespace TwinWidthI.FOInterp

open Finset

theorem lemma_8_5 (d ℓ : ℕ) :
    ∃ B : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
      (P : Finpartition (univ : Finset V)), TwinWidthI.BoolWidth.IsDPartition G P d → ∀ X ∈ P.parts,
        ((Eind G P (ℓ + 2)).connectedComponentMk '' (X : Set V)).ncard ≤ B := by sorry

end TwinWidthI.FOInterp
