-- Prove2me | Theorems.Thm_ScaleFreeDiam_Main_lemma_8
-- name    : ScaleFreeDiam.Main.lemma_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:12:01.49562+00:00
-- url     : https://prove2.me/theorems/fbe9411d-da58-4ecb-a122-0bc0b29c42b4
-- title:
--   Lemma 8, p. 21 — under E₁–E₅, w.p. 1 − o(1) every vertex has a descending path of length ≤ 8 log log n to a useful vertex
-- statement:
--   Assume $0<W_1<\dots<W_n<1$ satisfy $E_1,\dots,E_5$. With $\mathbb P_L$-probability $1-o(1)$, every vertex $v$ of $G=G(W_1,\dots,W_n)$ is joined by a descending path
--   $$
--   v=u_0>u_1>\dots>u_k,\qquad u_{t+1}\in\{l_{u_t,1},l_{u_t,2}\},\qquad k\le 8\log\log n,
--   $$
--   to a useful vertex $u_k$. Here $o(1)$ is a function of $n$ only, independent of $W$.
--
--   This lemma lets the expansion argument of §8, which starts from useful vertices, be applied to every vertex.
--
--   **Formalization Note** Following the convention of p. 20 ("the implicit bound in each occurrence of $o(\cdot)$ should be taken as a function of $n$ only, not depending on the $W_i$"), the statement is $\exists\,\delta\to0$ such that for all $n$ and all admissible $W$ satisfying $E_1,\dots,E_5$ the probability is at least $1-\delta(n)$. A path of length $0$ (when $v$ itself is useful) is allowed.
-- source:
--   Bollobás and Riordan, The diameter of a scale-free random graph, Combinatorica 24 (2004), p. 21, Lemma 8

import Mathlib
import Definitions.Def_ScaleFreeDiam_Main_Process
import Definitions.Def_ScaleFreeDiam_Main_EndpointModel

namespace ScaleFreeDiam.Main

open Filter Topology MeasureTheory ProbabilityTheory
open scoped Classical

theorem lemma_8 :
    ∃ δ : ℕ → ℝ, Tendsto δ atTop (𝓝 0) ∧
      ∀ (n : ℕ) (W : ℕ → ℝ), Admissible n W → E1 n W → E2 n W → E3 n W → E4 n W → E5 n W →
        1 - δ n ≤ probGW n W (fun l => ∀ v : ℕ, 1 ≤ v → v ≤ n →
          DescPathTo l v (8 * Real.log (Real.log n)) (useful n W)) := by sorry

end ScaleFreeDiam.Main
