-- Prove2me | Theorems.Thm_StrictCompatLB_MeanField_lemma_4_9
-- name    : StrictCompatLB.MeanField.lemma_4_9
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T06:51:41.136265+00:00
-- url     : https://prove2.me/theorems/1474cf53-17be-4ee6-8ae8-e1187bbe7edd
-- title:
--   Lemma 4.9 — stationary tail-moment bound Σ_{i≥k} E q_i ≤ ((1+λ)/2)/(1−(1+λ)/2) · E q_{k−1}
-- statement:
--   Let $0<\lambda<1$, $d\ge1$, and let $\{G_N\}_{N\ge1}$ be a sequence of connected graphs satisfying the subcriticality condition. There is $N_0\ge1$ such that for all $N\ge N_0$, for every stationary distribution of the JSQ(d) system on $G_N$ (with $\Phi(G_N,\infty)$ distributed according to it) and every $k\ge1$,
--   $$\sum_{i=k}^\infty\mathbb E\big[q_i(\Phi(G_N,\infty))\big]\;\le\;\frac{(1+\lambda)/2}{1-(1+\lambda)/2}\,\mathbb E\big[q_{k-1}(\Phi(G_N,\infty))\big].$$
--
--   Iterated over $k$, the bound gives geometric decay of the stationary tail occupancies uniformly in $N$, the key estimate for tightness.
--
--   **Formalization Note** Expectations and the series are computed in $[0,\infty]$, so the left side may a priori be infinite and the statement asserts that it is not when the right side is finite.
-- source:
--   Rutten & Mukherjee, Load Balancing Under Strict Compatibility Constraints, arXiv:2008.07562v2, p. 21, Lemma 4.9, (4.18); p. 50, App. H.3

import Mathlib
import Definitions.Def_StrictCompatLB_MeanField_Model

open Filter Topology MeasureTheory
open scoped ENNReal

namespace StrictCompatLB.MeanField

/-- Lemma 4.9 (p. 21; proof App. H.3, p. 50). For a sequence of connected graphs satisfying the
subcriticality condition, there is `N₀ ≥ 1` such that for all `N ≥ N₀`, every stationary
distribution `π` of the JSQ(d) chain on `G_N` and every `k ≥ 1`,
`∑_{i ≥ k} E_π[q_i] ≤ ((1+λ)/2) / (1 − (1+λ)/2) · E_π[q_{k−1}]` (expectations in `[0, ∞]`). -/
theorem lemma_4_9 (lam : ℝ) (hlam0 : 0 < lam) (hlam1 : lam < 1) (d : ℕ) (hd : 1 ≤ d)
    (M : ℕ → ℕ) (hM : ∀ N, 0 < M N) (G : (N : ℕ) → Finset (Fin N × Fin (M N)))
    (hconn : IsConnectedSeq M G) (hsub : IsSubcritical d M G) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ π : (Fin N → ℕ) → ℝ,
      IsStationary (jsqdKernel lam d M G N) π → ∀ k : ℕ, 1 ≤ k →
        (∑' i : ℕ, if k ≤ i then expectENN π (fun z => occ z i) else 0) ≤
          ENNReal.ofReal (((1 + lam) / 2) / (1 - (1 + lam) / 2)) *
            expectENN π (fun z => occ z (k - 1)) := by sorry

end StrictCompatLB.MeanField
