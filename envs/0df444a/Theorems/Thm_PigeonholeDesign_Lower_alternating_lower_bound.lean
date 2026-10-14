-- Prove2me | Theorems.Thm_PigeonholeDesign_Lower_alternating_lower_bound
-- name    : PigeonholeDesign.Lower.alternating_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T05:19:15.085979+00:00
-- url     : https://prove2.me/theorems/a1a5962d-a440-487b-b518-79c15075840d
-- title:
--   Proof of Lemma 4, p. ec15 — on the alternating instance the pigeonhole design has expected discrepancy ≥ c Σ_k (L_k − ε)√n_k
-- statement:
--   Let $0=l_0<l_1<\dots<l_K=1$ be breakpoints with cell lengths $L_k=l_k-l_{k-1}$, and consider the pigeonhole design with the interval pigeonholes $[l_0,l_1),\dots,[l_{K-2},l_{K-1}),[l_{K-1},l_K]$. Let $n_1,\dots,n_K$ be even nonnegative integers, let $T=\sum_k n_k$, and let $0<\epsilon<\min_k L_k$. The alternating instance places, cell after cell, $n_k/2$ consecutive pairs $(l_{k-1},l_k-\epsilon)$ (the pairs $(l_{K-1},l_K)$ in the last cell).
--
--   There is an absolute constant $c>0$, independent of $K$, of the breakpoints, of the counts and of $\epsilon$, such that the expected discrepancy of the pigeonhole design on this instance satisfies
--   $$\mathbb E\bigl[d_{A,B}\bigr]\;\ge\;c\sum_{k=1}^{K}(L_k-\epsilon)\sqrt{n_k}.$$
--
--   In each cell the first subject of every pair meets a tie and is assigned by a fair coin, and the second goes to the other group. The number of left points of cell $k$ in control is therefore binomial with $n_k/2$ trials and success probability $1/2$, and its deviation from $n_k/4$ forces a matching cost across the gap of the cell. This bound is the first step of the proof of Lemma 4.
--
--   **Formalization Note** The paper states the bound with $L_k$ and a cell-dependent constant $c_k$ and takes $c=\min_k c_k$. Here the factor is the exact gap width $L_k-\epsilon$ between the two points of a pair (the last cell's gap is $L_K\ge L_K-\epsilon$), and $c$ is a single absolute constant chosen before $K$. The counts $n_k$ are arbitrary even integers, not only the paper's choice $n_k=L_k^2T/\sum_i L_i^2$, which is in general not an integer. The proof's citation of Lemma EC.4 is read as Lemma EC.2, since the count is binomial. Cells are indexed from $0$ in Lean.
-- source:
--   Zhao and Zhou, Pigeonhole Design: Balancing Sequential Experiments from an Online Matching Perspective, arXiv:2201.12936v6, p. ec15, proof of Lemma 4 (arrival instance and per-pigeonhole bound c_k L_k (n_k)^{1/2})

import Mathlib
import Definitions.Def_PigeonholeDesign_Lower_Setting

namespace PigeonholeDesign.Lower

theorem alternating_lower_bound :
    ∃ c : ℝ, 0 < c ∧ ∀ (K : ℕ) (b : Breakpoints K) (n : Fin K → ℕ) (ε : ℝ),
      (∀ k, Even (n k)) → 0 < ε → (∀ k, ε < len b k) →
        c * ∑ k, (len b k - ε) * Real.sqrt (n k) ≤
          PigeonholeDesign.Upper.phdExp (intervalHole b) (altInstance b n ε (∑ k, n k)) := by sorry

end PigeonholeDesign.Lower
