-- Prove2me | Theorems.Thm_ScaleFreeDiam_Main_lemma_10
-- name    : ScaleFreeDiam.Main.lemma_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:12:08.08392+00:00
-- url     : https://prove2.me/theorems/ed8c9c18-9075-45bf-a7fe-bac4bd8f00e3
-- title:
--   Lemma 10, p. 22 — under E₁–E₅, a non-useful vertex i has ℙ_L(l_{i,1} useful) ≥ (log n)^{−3}
-- statement:
--   For all sufficiently large $n$ the following holds. Let $0<W_1<\dots<W_n<1$ satisfy $E_1,\dots,E_5$, and let $i$, $1\le i\le n$, be a vertex that is not useful. Then in $G(W_1,\dots,W_n)$
--   $$
--   \mathbb P_L\big(l_{i,1}\text{ is useful}\big)\ge(\log n)^{-3}.
--   $$
--   Together with Lemma 9 this gives Lemma 8: from every vertex a short descending path reaches a useful vertex.
--
--   **Formalization Note** "As usual we are assuming that $n$ is sufficiently large" (p. 22) is rendered as $\exists N_0\ \forall n\ge N_0\ \forall W$; the threshold does not depend on $W$ or $i$.
-- source:
--   Bollobás and Riordan, The diameter of a scale-free random graph, Combinatorica 24 (2004), p. 22, Lemma 10

import Mathlib
import Definitions.Def_ScaleFreeDiam_Main_Process
import Definitions.Def_ScaleFreeDiam_Main_EndpointModel

namespace ScaleFreeDiam.Main

open Filter Topology MeasureTheory ProbabilityTheory
open scoped Classical

theorem lemma_10 :
    ∃ N₀ : ℕ, ∀ n ≥ N₀, ∀ W : ℕ → ℝ, Admissible n W → E1 n W → E2 n W → E3 n W → E4 n W → E5 n W →
      ∀ i : ℕ, 1 ≤ i → i ≤ n → ¬ useful n W i →
        (Real.log n) ^ (-3 : ℤ) ≤ probGW n W (fun l => useful n W (lab l i 0)) := by sorry

end ScaleFreeDiam.Main
