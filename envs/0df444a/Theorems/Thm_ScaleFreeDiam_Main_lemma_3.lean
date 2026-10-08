-- Prove2me | Theorems.Thm_ScaleFreeDiam_Main_lemma_3
-- name    : ScaleFreeDiam.Main.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:11:06.810415+00:00
-- url     : https://prove2.me/theorems/44989f76-2500-4698-b2d1-64b0cbc4ce5b
-- title:
--   Lemma 3, p. 12 — events {g_{j_s} = i_s} with disjoint target sets are negatively correlated
-- statement:
--   In the process $G_1^N$, let
--   $$
--   E=\bigcap_{s=1}^{r}\{g_{j_s}=i_s\},\qquad E'=\bigcap_{s=1}^{r'}\{g_{j'_s}=i'_s\},
--   $$
--   where $1\le i_s<j_s\le N$ and $1\le i'_s<j'_s\le N$ for all $s$. If the sets $\{i_1,\dots,i_r\}$ and $\{i'_1,\dots,i'_{r'}\}$ are disjoint, then
--   $$
--   \mathbb P(E\cap E')\le\mathbb P(E)\,\mathbb P(E').
--   $$
--   This negative correlation lets the probability that a sparse graph appears in $G_1^N$ be bounded by a product over its parts (Lemma 4).
--
--   **Formalization Note** Each event is given by a finite set of pairs $(j,i)$; repeated pairs change nothing.
-- source:
--   Bollobás and Riordan, The diameter of a scale-free random graph, Combinatorica 24 (2004), p. 12, Lemma 3

import Mathlib
import Definitions.Def_ScaleFreeDiam_Main_Process

namespace ScaleFreeDiam.Main

open Filter Topology MeasureTheory ProbabilityTheory
open scoped Classical

theorem lemma_3 (N : ℕ) (E E' : Finset (ℕ × ℕ))
    (hE : ∀ p ∈ E, 1 ≤ p.2 ∧ p.2 < p.1 ∧ p.1 ≤ N)
    (hE' : ∀ p ∈ E', 1 ≤ p.2 ∧ p.2 < p.1 ∧ p.1 ≤ N)
    (hdisj : Disjoint (E.image Prod.snd) (E'.image Prod.snd)) :
    probG1 N (fun g => ∀ p ∈ E ∪ E', tgt g p.1 = p.2) ≤
      probG1 N (fun g => ∀ p ∈ E, tgt g p.1 = p.2) *
        probG1 N (fun g => ∀ p ∈ E', tgt g p.1 = p.2) := by sorry

end ScaleFreeDiam.Main
