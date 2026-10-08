-- Prove2me | Theorems.Thm_ScaleFreeDiam_Main_lemma_11
-- name    : ScaleFreeDiam.Main.lemma_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:12:12.245143+00:00
-- url     : https://prove2.me/theorems/ef6b5d2e-ae95-46e1-9ebb-89fab6af0ede
-- title:
--   Lemma 11, p. 23 — under E₁–E₅, a useful v is joined to 1 by a path of length ≤ (1/2+ε) log n/log log n w.p. 1 − o(n^{−1})
-- statement:
--   Assume $0<W_1<\dots<W_n<1$ satisfy $E_1,\dots,E_5$, let $\varepsilon>0$ be fixed, and let $v$, $1\le v\le n$, be a useful vertex. With $\mathbb P_L$-probability $1-o(n^{-1})$ there is a path in $G=G(W_1,\dots,W_n)$ between $v$ and $1$ of length at most
--   $$
--   \Big(\frac12+\varepsilon\Big)\frac{\log n}{\log\log n}.
--   $$
--   Here $o(n^{-1})$ is a function of $n$ (and $\varepsilon$) only, independent of $W$ and $v$. Applied to every useful vertex and combined with Lemma 8, it bounds the diameter of $G$.
--
--   **Formalization Note** $1-o(n^{-1})$ is rendered as $1-\delta(n)/n$ with $\delta(n)\to0$, $\delta$ chosen after $\varepsilon$ and before $n$, $W$, $v$ (the convention of p. 20). The path is a walk in the simple-graph shadow of $G$, which is equivalent for length bounds.
-- source:
--   Bollobás and Riordan, The diameter of a scale-free random graph, Combinatorica 24 (2004), p. 23, Lemma 11

import Mathlib
import Definitions.Def_ScaleFreeDiam_Main_Process
import Definitions.Def_ScaleFreeDiam_Main_EndpointModel

namespace ScaleFreeDiam.Main

open Filter Topology MeasureTheory ProbabilityTheory
open scoped Classical

theorem lemma_11 (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℕ → ℝ, Tendsto δ atTop (𝓝 0) ∧
      ∀ (n : ℕ) (W : ℕ → ℝ), Admissible n W → E1 n W → E2 n W → E3 n W → E4 n W → E5 n W →
        ∀ (v : ℕ) (hv1 : 1 ≤ v) (hvn : v ≤ n), useful n W v →
          1 - δ n / n ≤ probGW n W (fun l =>
            ∃ p : (GW l).Walk ⟨v - 1, by omega⟩ ⟨0, by omega⟩,
              (p.length : ℝ) ≤ (1 / 2 + ε) * Real.log n / Real.log (Real.log n)) := by sorry

end ScaleFreeDiam.Main
