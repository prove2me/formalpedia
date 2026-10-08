-- Prove2me | Theorems.Thm_TwinWidthI_FOInterp_theorem_8_3
-- name    : TwinWidthI.FOInterp.theorem_8_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:44:40.676151+00:00
-- url     : https://prove2.me/theorems/10fd150e-1ff6-4372-a951-156649738c05
-- title:
--   Theorem 8.3 — a prenex first-order interpretation of a bounded-twin-width graph class has bounded twin-width
-- statement:
--   **Theorem 8.3 (graphs).** For every prenex first-order formula $\varphi(x,y)$ with two free variables and every bounded-twin-width class $\mathcal G$ of graphs, the class $\varphi(\mathcal G)$ also has bounded twin-width.
--
--   Precisely: for every prenex formula $\varphi(x,y)$ in the language of graphs and every integer $d\ge 0$ there is an integer $D$ such that, for every finite simple graph $G$ with $\operatorname{tww}(G)\le d$ and every vertex set $S\subseteq V(G)$,
--   $$\operatorname{tww}\bigl(\varphi(G)[S]\bigr)\le D .$$
--   Here $\varphi(G)$ is the interpretation of $G$ by $\varphi$ (distinct $u,v$ adjacent iff $G\models\varphi(u,v)\wedge\varphi(v,u)$), and $\varphi(G)[S]$ is its induced subgraph on $S$; $\varphi(\mathcal G)$ is the class of all induced subgraphs of graphs $\varphi(G)$, $G\in\mathcal G$.
--
--   Consequently, for instance, fixed powers of graphs of bounded twin-width have bounded twin-width, and, combined with Lemma 8.2, so do first-order transductions (Theorem 8.1).
--
--   **Formalization Note.** The page states Theorem 8.3 for augmented binary structures; Section 8 says "for the sake of simplicity, we will stick to undirected graphs" (p. 3:40) and the proof is written for graphs, so this is the graph case. A class has bounded twin-width when one $d$ bounds all its members; taking the class of all graphs of twin-width at most $d$ is no loss of generality. The bound $D$ depends only on $\varphi$ and $d$: it is chosen before the vertex type, the graph and the subset. The edge relation of $\varphi(G)$ requires $u\neq v$ because $\varphi(G)$ is a simple graph.
-- source:
--   Bonnet, Kim, Thomassé and Watrigant, Twin-width I: Tractable FO Model Checking, J. ACM 69(1), Article 3 (2021), p. 3:41, Theorem 8.3 (graph case; definitions of φ(G) and φ(𝒢) on p. 3:40)

import Mathlib
import Definitions.Def_TwinWidthI_FOInterp_Setting

namespace TwinWidthI.FOInterp

open Finset FirstOrder FirstOrder.Language

theorem theorem_8_3 (φ : Language.graph.Formula (Fin 2)) (hφ : φ.IsPrenex) (d : ℕ) :
    ∃ D : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V), TwinWidthI.BoolWidth.TwinWidthLE G d →
      ∀ S : Finset V, TwinWidthI.BoolWidth.TwinWidthLE ((interp φ G).induce (S : Set V)) D := by sorry

end TwinWidthI.FOInterp
