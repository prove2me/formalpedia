-- Prove2me | Theorems.Thm_SecondBestBT_lemma_5_11
-- name    : SecondBestBT.lemma_5_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:47:57.02589+00:00
-- url     : https://prove2.me/theorems/1b276706-7ac3-470b-8a64-95a7d5a97cb6
-- title:
--   Lemma 5.11 — Algorithm 1 never fails for full-support regular sellers at $\beta=1/2$
-- statement:
--   Let $\alpha\ge0$, $\beta=\tfrac12$, and let $F_S$ be $\alpha$-weakly regular with full support on $\{0,\dots,K\}$, where $K\ge0$. Then Algorithm 1 never returns fail, even when buyer values exceed $K$: for every buyer value $b\in\mathbb N$, the run through $b$ succeeds.
--
--   Together with Theorem 4.10 this gives a buyer-independent certificate for every full-support regular seller.
--
--   Differences from the source:
--   - encoding: "Algorithm 1 never returns fail" → `greedyRun α (1/2) K f_S b ≠ none` for every $b\in\mathbb N$; reason: `none` is fail; a failure at some $b$ persists to all later $b$
-- source:
--   Liu–Qin–Ren–Wang, Second-Best Bilateral Trade is 1/2 Efficient, arXiv:2606.03849 (held version, sha256 17184930…), Lemma 5.11, p.24

import Mathlib
import Definitions.Def_SecondBestBT_IsFullSupportOn
import Definitions.Def_SecondBestBT_IsAlphaWeaklyRegular
import Definitions.Def_SecondBestBT_greedyRun

namespace SecondBestBT

/-- **Lemma 5.11** (non-failure for full-support regular sellers; Liu–Qin–Ren–Wang, *Second-Best
Bilateral Trade is 1/2 Efficient*, arXiv:2606.03849, held version sha256 17184930…, Lemma 5.11,
p.24). Let `α ≥ 0`, `β = 1/2`, and let `F_S` be `α`-weakly regular with full support on
`{0, …, K}`, `K ≥ 0`. Algorithm 1 never returns fail, even when buyer values exceed `K`.

**Formalization Note** "Never returns fail" is: the run through every buyer value `b ∈ ℕ` is not
`none`. -/
theorem lemma_5_11 (α : ℝ) (hα : 0 ≤ α) (K : ℕ) (fS : ℕ → ℝ) (hfS : IsFullSupportOn fS K)
    (hreg : IsAlphaWeaklyRegular α fS K) :
    ∀ b : ℕ, greedyRun α (1 / 2) K fS b ≠ none := by sorry

end SecondBestBT
