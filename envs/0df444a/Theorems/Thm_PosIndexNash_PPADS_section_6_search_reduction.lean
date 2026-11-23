-- Prove2me | Theorems.Thm_PosIndexNash_PPADS_section_6_search_reduction
-- name    : PosIndexNash.PPADS.section_6_search_reduction
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T02:59:42.800159+00:00
-- url     : https://prove2.me/theorems/d57c7711-cbf9-4162-a3d9-eac0f73d0547
-- title:
--   Section 6 — positive exact LCP solutions reduce to positive-index Nash equilibria
-- statement:
--   The imitation-game construction and effective perturbation of §6 give a polynomial-time search reduction
--   $$\textsc{Positive-Index LCP}\le_p\textsc{Positive-Index Nash}.$$
--   For $N=m+1$, the instance map forms $S=(-M,b+\mathbf1;\mathbf0^\top,1)$, shifts its entries by a sufficiently large integer $c$, and applies Lemma 6.6 with $\varepsilon=2^{-\kappa}$. The output game is rational and globally nondegenerate. Lemmas 6.2–6.3 identify its equilibria with LCP solutions, and Lemmas 6.5–6.6 preserve the index.
--
--   For the answer map, Lemma 6.7 reads the common equilibrium support $K=I\cup\{\star\}$ and recovers the unique rational LCP solution by
--   $$x_I=M_{I,I}^{-1}b_I,\qquad x_{[m]\setminus I}=0.$$
--   An index-$+1$ Nash answer therefore decodes in polynomial time to an LCP answer with $\operatorname{sign}\det M_{I,I}=+1$.
-- source:
--   Kontogiannis, Panageas, Pollatos, Yan, Finding a Positive Index Nash Equilibrium is PPADS-Complete, arXiv:2609.23879, pp. 40–44, Lemmas 6.2–6.5; pp. 44–50, Lemma 6.6; p. 51, Lemma 6.7 and proof of Theorem 6.8

import Mathlib
import Definitions.Def_CardinalMatching_SearchReduces
import Definitions.Def_PosIndexNash_PPADS_PositiveIndexLCP
import Definitions.Def_PosIndexNash_PPADS_PositiveIndexNash

theorem PosIndexNash.PPADS.section_6_search_reduction :
    CardinalMatching.SearchReduces PositiveIndexLCP PositiveIndexNash := by sorry
