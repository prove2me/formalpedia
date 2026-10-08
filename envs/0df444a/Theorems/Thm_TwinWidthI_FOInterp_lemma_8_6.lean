-- Prove2me | Theorems.Thm_TwinWidthI_FOInterp_lemma_8_6
-- name    : TwinWidthI.FOInterp.lemma_8_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:45:43.838581+00:00
-- url     : https://prove2.me/theorems/6a056b23-a92b-413c-b0f2-7013d05f589a
-- title:
--   Lemma 8.6 — vertices of one I_{ℓ+2}-part are not distinguished by a prenex formula from a far part
-- statement:
--   Let $\varphi(x,y)$ be a prenex formula of depth $\ell$. Let $\mathcal P$ be a $d$-partition of a finite simple graph $G$, and let $X,Y$ be two parts of $\mathcal P$ at distance at least $3^{\ell+2}$ in the red graph $G_{\mathcal P}$. Let $X',Y'$ be two parts of $I_{\ell+2}(G,\mathcal P)$ contained in $X$ and $Y$ respectively. Then for $u\in X'$ and $v,v'\in Y'$,
--   $$G\models\varphi(u,v)\iff G\models\varphi(u,v').$$
--
--   By symmetry $X'$ and $Y'$ are then homogeneous in $\varphi(G)$, so in the partition $I_{\ell+2}(G,\mathcal P)$ of $\varphi(G)$ only parts at bounded distance in $G_{\mathcal P}$ can be non-homogeneous. This is the bounded-red-degree half of the proof of Theorem 8.3.
--
--   **Formalization Note.** Graph case (the page says "augmented binary structure"; Section 8 works with graphs, p. 3:40). Distances in $G_{\mathcal P}$ are extended distances in $\mathbb N\cup\{\infty\}$, so parts in different components of $G_{\mathcal P}$ count as far apart. $u\in X'\subseteq X$ is written $u\in X$, and $v,v'\in Y'\subseteq Y$ is written as $v,v'\in Y$ and $v,v'$ in the same connected component of `Eind G P (ℓ + 2)`.
-- source:
--   Bonnet, Kim, Thomassé and Watrigant, Twin-width I: Tractable FO Model Checking, J. ACM 69(1), Article 3 (2021), p. 3:43, Lemma 8.6 (graph case, §8 p. 3:40)

import Mathlib
import Definitions.Def_TwinWidthI_FOInterp_Setting
import Definitions.Def_TwinWidthI_FOInterp_MorphismTree

namespace TwinWidthI.FOInterp

open Finset FirstOrder FirstOrder.Language

theorem lemma_8_6 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (d ℓ : ℕ)
    (φ : Language.graph.Formula (Fin 2)) (hφ : IsPrenexOfDepth φ ℓ)
    (P : Finpartition (univ : Finset V)) (hP : TwinWidthI.BoolWidth.IsDPartition G P d)
    (X Y : Finset V) (hX : X ∈ P.parts) (hY : Y ∈ P.parts)
    (hXY : ((3 ^ (ℓ + 2) : ℕ) : ℕ∞) ≤ (redGraph G P).edist X Y)
    (u v v' : V) (hu : u ∈ X) (hv : v ∈ Y) (hv' : v' ∈ Y)
    (hvv' : (Eind G P (ℓ + 2)).Reachable v v') :
    letI := G.structure
    φ.Realize ![u, v] ↔ φ.Realize ![u, v'] := by sorry

end TwinWidthI.FOInterp
