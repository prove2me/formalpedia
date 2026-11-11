-- Prove2me | Theorems.Thm_RandKSATSample_Main_lemma_3_3
-- name    : RandKSATSample.Main.lemma_3_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:00:09.610208+00:00
-- url     : https://prove2.me/theorems/d9902af8-21ce-419f-9990-9b4980883b6f
-- title:
--   Lemma 3.3 — at most r high-degree variables, with probability ≥ 1 − e^{−⌈q0 n⌉}
-- statement:
--   For $k\ge30$ and $h=\lceil q_0n\rceil$, with $V_{\mathrm{high}}=\{v:\deg(v)\ge\Delta\}$, $\Delta=6k^7\lambda$ and $r=\lfloor q_0n\rfloor$,
--   $$\Pr_{\Phi\sim\Phi(k,n,m)}\big(|V_{\mathrm{high}}|\le r\big)\ \ge\ 1-e^{-h}.$$
--   Few high-degree variables keep the core small.
--
--   Differences from the source: none.
-- source:
--   He, Li, Yang, Fast Almost-Uniform Sampling of Random k-SAT Solutions, arXiv:2610.10474 (version not printed; file sha256 563a4d84…), p. 14, Lemma 3.3

import Mathlib
import Definitions.Def_RandKSATSample_Main_Formula
import Definitions.Def_RandKSATSample_Main_Structure

set_option autoImplicit false

namespace RandKSATSample.Main

/-- Lemma 3.3: for `k ≥ 30` and `h = ⌈q0 n⌉`, `P(|V_high| ≤ r) ≥ 1 − e^{−h}`. -/
theorem lemma_3_3 (n m k : ℕ) (hk : 30 ≤ k) :
    1 - Real.exp (-(⌈q0 n m k * n⌉₊ : ℝ)) ≤ probF n m k (fun Φ => FewHigh Φ) := by sorry

end RandKSATSample.Main
