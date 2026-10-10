-- Prove2me | Theorems.Thm_RunIntersect_Tight_lemma_4
-- name    : RunIntersect.Tight.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T15:35:44.223644+00:00
-- url     : https://prove2.me/theorems/d73a7dcf-4717-4440-9d14-84dfce3df6de
-- title:
--   Lemma 4, p. 1018 — G is β-acyclic iff every subset of its edges has the running intersection property
-- statement:
--   A hypergraph $G=(V,E)$ is β-acyclic if and only if every subset $E'\subseteq E$ of its edges has the running intersection property:
--   $$G\ \text{β-acyclic}\iff\forall E'\subseteq E,\ \exists\text{ an ordering }p_1,\dots,p_m\text{ of }E'\text{ with } p_k\cap\textstyle\bigcup_{i<k}p_i\subseteq p_j\text{ for some }j<k,\ k\ge 2.$$
--
--   The result is due to Beeri, Fagin, Maier and Yannakakis (1983); the paper quotes it without proof. It provides the running intersection ordering of the maximal edges on which the construction of $G^+$ and the induction of Theorem 3 rest.
--
--   **Formalization Note** $E'$ is a finite set of edges, viewed as a multiset without repetitions; the empty set of edges has the (empty) running intersection ordering.
-- source:
--   Del Pia and Khajavirad, The running intersection relaxation of the multilinear polytope, Math. Oper. Res. 46 (2021), p. 1018, Lemma 4 (from Beeri et al., J. ACM 30 (1983))

import Mathlib
import Definitions.Def_RunIntersect_Tight_Setting

namespace RunIntersect.Tight

theorem lemma_4 {α : Type*} [Fintype α] [DecidableEq α] (G : Hypergraph α) :
    IsBetaAcyclic G ↔ ∀ E' ⊆ G.E, HasRIP E'.val := by sorry

end RunIntersect.Tight
