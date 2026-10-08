-- Prove2me | Theorems.Thm_TwinWidthI_FOInterp_lemma_8_4
-- name    : TwinWidthI.FOInterp.lemma_8_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:45:20.503759+00:00
-- url     : https://prove2.me/theorems/5d6ad01d-2038-4117-bb48-2bf16759b34e
-- title:
--   Lemma 8.4 — if (u, v) and (u, v′) are equivalent in MT_{ℓ+2}(G), no prenex formula of depth ℓ distinguishes them
-- statement:
--   Let $G$ be a finite simple graph, $\ell\ge 0$, and $u,v,v'$ vertices of $G$. Suppose the nodes $(u,v)$ and $(u,v')$ are equivalent siblings in the complete morphism-tree $MT_{\ell+2}(G)$. Then for every prenex formula $\varphi(x,y)$ of depth $\ell$,
--   $$G\models\varphi(u,v)\iff G\models\varphi(u,v').$$
--
--   The subtree of $MT_{\ell+2}(G)$ below $(a,b)$ is the game tree in which the quantifiers of $\varphi$ choose $x_1,\dots,x_\ell$; an automorphism swapping the two nodes transports one evaluation onto the other. This lemma links the combinatorics of morphism-trees with first-order truth, and Lemma 8.6 rests on it.
--
--   **Formalization Note.** The page states the lemma for augmented binary structures; Section 8 works with undirected graphs ("for the sake of simplicity, we will stick to undirected graphs", p. 3:40), and so does this statement. "In $MT_{\ell+2}(G)$" means equivalence with respect to the one-part partition. Free variable `0` of $\varphi$ is $x$ and free variable `1` is $y$; the formula is evaluated in `G.structure`.
-- source:
--   Bonnet, Kim, Thomassé and Watrigant, Twin-width I: Tractable FO Model Checking, J. ACM 69(1), Article 3 (2021), p. 3:41, Lemma 8.4 (graph case, §8 p. 3:40)

import Mathlib
import Definitions.Def_TwinWidthI_FOInterp_Setting
import Definitions.Def_TwinWidthI_FOInterp_MorphismTree

namespace TwinWidthI.FOInterp

open Finset FirstOrder FirstOrder.Language

theorem lemma_8_4 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (ℓ : ℕ)
    (u v v' : V) (h : EquivSiblings G ⊤ (MT V (ℓ + 2)) [u] v v')
    (φ : Language.graph.Formula (Fin 2)) (hφ : IsPrenexOfDepth φ ℓ) :
    letI := G.structure
    φ.Realize ![u, v] ↔ φ.Realize ![u, v'] := by sorry

end TwinWidthI.FOInterp
