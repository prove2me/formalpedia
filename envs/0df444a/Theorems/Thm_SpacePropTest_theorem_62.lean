-- Prove2me | Theorems.Thm_SpacePropTest_theorem_62
-- name    : SpacePropTest.theorem_62
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:55:43.349533+00:00
-- url     : https://prove2.me/theorems/666e58da-ba3e-440c-8fa1-14a6d0c8cbd9
-- title:
--   Theorem 62, p.53 — Markov chain tree theorem: $\hat p_C(s)=\|W_s(C)\|/\|W(C)\|$
-- statement:
--   Let $C$ be a Markov chain on a finite state set with start state $s^\star$. For every state $s$ the Cesàro averages $\frac1T\sum_{t<T}\Pr[C\text{ is in state }s\text{ at time }t]$ converge, and the long-run probability is
--
--   $$\hat p_C(s)=\frac{\|W_s(C)\|}{\|W(C)\|},$$
--
--   with the arborescence weights of Definitions 60–61.
--
--   The lower bounds use it to turn multiplicative closeness of transition probabilities into closeness of long-run probabilities (Lemma 10).
--
--   Differences from the source:
--   - encoding: $\hat p_C(s):=\lim_{T\to\infty}\cdots$, then $\hat p_C(s)=\|W_s(C)\|/\|W(C)\|$ → the Cesàro sequence tends to $\|W_s(C)\|/\|W(C)\|$, and `longRun` equals it; reason: the paper's $\lim$ presupposes convergence; stating it with `Tendsto` makes the existence explicit
--   - encoding: arborescence as a set $F$ of edges → arborescence as a parent map (`none` at roots, `some v` for the edge $u\to v$); reason: a forest directed toward its roots with outdegree $\le1$ is the same as its parent map
-- source:
--   Canonne, Chen, Pires, Pitassi, Servedio, The Space Complexity of Property Testing, manuscript of November 2, 2026 (sha256 65850aa6…), Theorem 62, p.53 (PDF 55); Definitions 60–61, p.52 (PDF 54)

import Mathlib
import Definitions.Def_SpacePropTest_MarkovChain
import Definitions.Def_SpacePropTest_ChainTree

set_option autoImplicit false

namespace SpacePropTest

open Filter Topology in
/-- **Theorem 62 (Markov chain tree theorem)** (C. Canonne, X. Chen, W. Pires, T. Pitassi,
R. A. Servedio, *The Space Complexity of Property Testing*, manuscript of November 2, 2026,
sha256 65850aa6…; App. A.1, p.53 (PDF 55); after [LR83]). Let `C` be a Markov chain over a finite
state space with start state `s⋆`. For every state `s`, the long-run probability
`p̂_C(s) = lim_{T→∞} (1/T) ∑_{t<T} Pr[C is in state s at time t]` exists and equals
`‖W_s(C)‖/‖W(C)‖`.

**Formalization Note.** The limit is stated with `Tendsto`, so its existence is part of the
statement; the second conjunct restates it for `longRun`. Arborescences are parent maps
(Definition 61; see `IsArborescence`). -/
theorem theorem_62 {σ : Type*} [Fintype σ] [DecidableEq σ] (C : Matrix σ σ ℝ)
    (hC : IsStochastic C) (s₀ s : σ) :
    Tendsto (cesaro C s₀ s) atTop (𝓝 (WnormAt C s₀ s / Wnorm C)) ∧
      longRun C s₀ s = WnormAt C s₀ s / Wnorm C := by sorry

end SpacePropTest
