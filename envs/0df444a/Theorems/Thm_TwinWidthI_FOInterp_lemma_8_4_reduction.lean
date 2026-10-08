-- Prove2me | Theorems.Thm_TwinWidthI_FOInterp_lemma_8_4_reduction
-- name    : TwinWidthI.FOInterp.lemma_8_4_reduction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:45:37.18395+00:00
-- url     : https://prove2.me/theorems/59e08ab8-6081-4cd2-bfcc-0fe27cb9a229
-- title:
--   §8, p. 3:42 — Lemma 8.4 holds for equivalent nodes in any reduction of MT_{ℓ+2}(G, P)
-- statement:
--   Let $G$ be a finite simple graph with a partition $\mathcal P$, $\ell\ge 0$, and let $T$ be a reduction of $MT_{\ell+2}(G,\mathcal P)$, reductions performed in $(G,\mathcal P)$. If the nodes $(u,v)$ and $(u,v')$ are equivalent siblings in $T$ (with respect to $(G,\mathcal P)$), then for every prenex formula $\varphi(x,y)$ of depth $\ell$,
--   $$G\models\varphi(u,v)\iff G\models\varphi(u,v').$$
--
--   This is the consequence of Lemma 8.4 noted at the top of p. 3:42; it is the form used at the end of the proof of Lemma 8.6.
--
--   **Formalization Note.** Graph case, as for Lemma 8.4. The partition $\mathcal P$ is arbitrary; for the one-part partition and $T=MT_{\ell+2}(G)$ this is Lemma 8.4.
-- source:
--   Bonnet, Kim, Thomassé and Watrigant, Twin-width I: Tractable FO Model Checking, J. ACM 69(1), Article 3 (2021), p. 3:42, §8, "A consequence of Lemma 8.4 is that if (u,v) and (u,v′) are equivalent nodes in a reduction (T,m) of MT_{ℓ+2}(G)"

import Mathlib
import Definitions.Def_TwinWidthI_FOInterp_Setting
import Definitions.Def_TwinWidthI_FOInterp_MorphismTree

namespace TwinWidthI.FOInterp

open Finset FirstOrder FirstOrder.Language

theorem lemma_8_4_reduction {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (P : Finpartition (univ : Finset V)) (ℓ : ℕ) (T : Set (List V))
    (hT : IsReduction G P (MT V (ℓ + 2)) T) (u v v' : V) (h : EquivSiblings G P T [u] v v')
    (φ : Language.graph.Formula (Fin 2)) (hφ : IsPrenexOfDepth φ ℓ) :
    letI := G.structure
    φ.Realize ![u, v] ↔ φ.Realize ![u, v'] := by sorry

end TwinWidthI.FOInterp
