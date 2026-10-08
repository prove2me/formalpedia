-- Prove2me | Theorems.Thm_ScaleFreeDiam_Main_upper_bound_given_W
-- name    : ScaleFreeDiam.Main.upper_bound_given_W
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:12:13.917281+00:00
-- url     : https://prove2.me/theorems/feec57b5-87c0-4964-b109-c2f96c092e2b
-- title:
--   Proof of Theorem 1, p. 29 — under E₁–E₅, ℙ_L(diam G(W) > (1+ε/2) log n/log log n + 16 log log n) = o(1)
-- statement:
--   Let $\varepsilon>0$. There is a function $\delta(n)\to0$ such that for every $n$ and every $0<W_1<\dots<W_n<1$ satisfying $E_1,\dots,E_5$,
--   $$
--   \mathbb P_L\Big(\operatorname{diam}\big(G(W_1,\dots,W_n)\big)>\Big(1+\frac\varepsilon2\Big)\frac{\log n}{\log\log n}+16\log\log n\Big)\le\delta(n).
--   $$
--   This display is the step of the proof of Theorem 1 that combines Lemmas 8 and 11 (applied with $\varepsilon/4$); together with Lemma 7 and the coupling of §6 it yields the upper bound of Theorem 1.
--
--   **Formalization Note** "$\operatorname{diam}>x$" is the negation of `AllWithin`, so a disconnected $G(W)$ counts as a failure. The $o(1)$ is a function of $n$ (and $\varepsilon$) only, quantified before $W$ (convention of p. 20).
-- source:
--   Bollobás and Riordan, The diameter of a scale-free random graph, Combinatorica 24 (2004), p. 29, proof of Theorem 1 (first display)

import Mathlib
import Definitions.Def_ScaleFreeDiam_Main_Process
import Definitions.Def_ScaleFreeDiam_Main_EndpointModel

namespace ScaleFreeDiam.Main

open Filter Topology MeasureTheory ProbabilityTheory
open scoped Classical

theorem upper_bound_given_W (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℕ → ℝ, Tendsto δ atTop (𝓝 0) ∧
      ∀ (n : ℕ) (W : ℕ → ℝ), Admissible n W → E1 n W → E2 n W → E3 n W → E4 n W → E5 n W →
        probGW n W (fun l => ¬ AllWithin (GW l)
          ((1 + ε / 2) * Real.log n / Real.log (Real.log n) + 16 * Real.log (Real.log n)))
          ≤ δ n := by sorry

end ScaleFreeDiam.Main
