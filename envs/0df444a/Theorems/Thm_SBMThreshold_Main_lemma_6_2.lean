-- Prove2me | Theorems.Thm_SBMThreshold_Main_lemma_6_2
-- name    : SBMThreshold.Main.lemma_6_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:17:48.008987+00:00
-- url     : https://prove2.me/theorems/c4e8f50a-673c-4df9-9338-83e99e1f5534
-- title:
--   Lemma 6.2, p. 27 — if ℓ log d = o(log n) then P[G is ℓ-tangle-free] ≥ 1 − n^{−1+o(1)}
-- statement:
--   Let $a_n,b_n>0$ and $\ell_n$ satisfy Assumption 2.7: $d_n,|s_n|=n^{o(1/\log\log n)}$ and $\log\log n\ll\ell_n\ll\sqrt{\log n}$. Let $\Xi$ be the event that $G\sim\mathcal G(n,a_n/n,b_n/n)$ contains no $\ell_n$-tangle. If $\ell_n\log d_n=o(\log n)$, then there is a sequence $c_n\to0$ such that for all $n$
--   $$
--   \mathbb P[\Xi]\ge 1-n^{-1+c_n}.
--   $$
--
--   Sparse random graphs are locally tree-like with at most one cycle in each small neighbourhood; this lemma quantifies it. Conditioning on $\Xi$ removes the rare dense structures (such as cliques) that would otherwise dominate the expectation of $N^{(k)}_{u,v}$.
--
--   **Formalization Note** $n^{-1+o(1)}$ is unfolded as $n^{-1+c_n}$ with an explicit sequence $c_n\to0$. Assumption 2.7, stated on p. 5 "for the rest of this article", is kept as a hypothesis: the lemma's own condition $\ell\log d=o(\log n)$ does not by itself bound $\ell$ when $d$ is close to $1$. For small $n$ the edge weights may not be probabilities; the bound is asymptotic, and $c_n$ absorbs finitely many $n$.
-- source:
--   Mossel, Neeman and Sly, A Proof of the Block Model Threshold Conjecture, arXiv:1311.4115v4, p. 27, Lemma 6.2 (with Assumption 2.7, p. 5)

import Mathlib
import Definitions.Def_SBMThreshold_Main_Setting
import Definitions.Def_SBMThreshold_Main_Paths
open Filter Topology Finset

namespace SBMThreshold.Main

/-- Lemma 6.2 (p. 27): under Assumption 2.7, if `ℓ log d = o(log n)` then the probability that
`G` is ℓ-tangle-free is at least `1 - n^{-1+o(1)}`. -/
theorem lemma_6_2 (a b : ℕ → ℝ) (ℓ : ℕ → ℕ) (hA : Assumption27 a b ℓ)
    (hℓd : Tendsto (fun n : ℕ => (ℓ n : ℝ) * Real.log (dPar (a n) (b n)) / Real.log n)
      atTop (𝓝 0)) :
    ∃ c : ℕ → ℝ, Tendsto c atTop (𝓝 0) ∧ ∀ n : ℕ,
      1 - sbmProb n (a n) (b n) (fun _ G => TangleFree (ℓ n) G) ≤ (n : ℝ) ^ (-1 + c n) := by sorry

end SBMThreshold.Main
