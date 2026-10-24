-- Prove2me | Theorems.Thm_SubsampleSubmod_SampleGreedy_lemma_10
-- name    : SubsampleSubmod.SampleGreedy.lemma_10
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T23:08:59.259981+00:00
-- url     : https://prove2.me/theorems/8c51d124-b13b-46c6-9e4f-8821746887ad
-- title:
--   Lemma 10, p. 16 — with q = 1/p, E[|O_u| − Y_u] ≤ (p−1)/p · E[X_u] (7)
-- statement:
--   Let $(\mathcal N, \mathcal I)$ be a $p$-extendible independence system with $p \ge 1$, $T \in \mathcal I$ and $f$ a set function. Run Algorithm 2 from $O = T$ with every coin showing $1$ independently with probability $q = \frac1p$; let $X_u$ indicate that $u$ is considered and $Y_u$ that $u$ was added to $S$ while $u \notin O$ at the beginning of its iteration. Then for every $u \in \mathcal N$,
--   $$\mathbb E\big[|O_u| - Y_u\big] \;\le\; \frac{p-1}{p}\,\mathbb E[X_u]. \tag{7}$$
--
--   Together with Lemmas 8 and 9 this gives the $p$-approximation for linear objectives.
--
--   **Formalization Note** $|O_u| - Y_u$ is computed in $\mathbb R$ (it can be $-1$). For $p = 1$ the sampling probability is $q = 1$ and every coin shows $1$.
-- source:
--   Harshaw et al., arXiv:2104.02772v1, p. 16, Lemma 10, inequality (7)

import Mathlib
import Definitions.Def_SubsampleSubmod_SampleGreedy_Analysis

namespace SubsampleSubmod.SampleGreedy

/-- Lemma 10 (p. 16), inequality (7). With sampling probability `q = 1/p`, for every element `u`:
`E[|O_u| − Y_u] ≤ (p − 1)/p · E[X_u]` for Algorithm 2 run from an independent `T` over a
`p`-extendible system. -/
theorem lemma_10 {α : Type} [Fintype α] [LinearOrder α] (f : Finset α → ℝ)
    (I : Finset α → Prop) (p : ℕ) (hp : 1 ≤ p) (hI : IsIndepSystem I)
    (hext : IsPExtendible p I) (T : Finset α) (hT : I T) (u : α) :
    E2 (1 / (p : ℝ)) f I T
        (fun st => ((st.Ou u).card : ℝ) - (if u ∈ st.Y then (1 : ℝ) else 0)) ≤
      (((p : ℝ) - 1) / (p : ℝ)) *
        E2 (1 / (p : ℝ)) f I T (fun st => if u ∈ st.considered then (1 : ℝ) else 0) := by sorry

end SubsampleSubmod.SampleGreedy
