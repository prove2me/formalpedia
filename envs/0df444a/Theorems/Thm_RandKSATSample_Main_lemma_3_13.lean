-- Prove2me | Theorems.Thm_RandKSATSample_Main_lemma_3_13
-- name    : RandKSATSample.Main.lemma_3_13
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:59:58.650862+00:00
-- url     : https://prove2.me/theorems/7e31d91d-f6ab-4ba3-b045-27cf1c60e886
-- title:
--   Lemma 3.13 — Φ(k, n, ⌊αn⌋) is nice (Condition 3.12) with probability 1 − o_n(1)
-- statement:
--   Fix an integer $k\ge2^{20}$ and a real density $0<\alpha\le2^k/k^{16}$. For $\Phi\sim\Phi(k,n,\lfloor\alpha n\rfloor)$,
--   $$\lim_{n\to\infty}\Pr\big[\Phi\text{ satisfies Condition 3.12}\big]=1.$$
--   Condition 3.12 collects the parameter conditions, the structural events of Lemmas 3.1–3.3 and the polymer-root estimate, everything the analysis of the sampler uses about the formula.
--
--   Differences from the source:
--   - encoding: with probability 1 − o_n(1) for all sufficiently large n → Tendsto (n ↦ P[Nice]) atTop (𝓝 1); reason: the same statement
-- source:
--   He, Li, Yang, Fast Almost-Uniform Sampling of Random k-SAT Solutions, arXiv:2610.10474 (version not printed; file sha256 563a4d84…), p. 20, Lemma 3.13

import Mathlib
import Definitions.Def_RandKSATSample_Main_Formula
import Definitions.Def_RandKSATSample_Main_Structure

set_option autoImplicit false

open Filter Topology

namespace RandKSATSample.Main

/-- Lemma 3.13: for an integer `k ≥ 2^20` and a real density `0 < α ≤ 2^k/k^16`, the random
formula `Φ(k, n, ⌊αn⌋)` satisfies Condition 3.12 with probability `1 − o_n(1)`. -/
theorem lemma_3_13 (k : ℕ) (hk : 2 ^ 20 ≤ k) (α : ℝ) (hα0 : 0 < α)
    (hα : α ≤ (2 : ℝ) ^ k / (k : ℝ) ^ 16) :
    Tendsto (fun n : ℕ => probF n ⌊α * n⌋₊ k (fun Φ => Nice Φ)) atTop (𝓝 1) := by sorry

end RandKSATSample.Main
