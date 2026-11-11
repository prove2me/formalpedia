-- Prove2me | Theorems.Thm_RandKSATSample_Main_lemma_3_2
-- name    : RandKSATSample.Main.lemma_3_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:00:20.821918+00:00
-- url     : https://prove2.me/theorems/99bcb639-ac68-4ed7-ae32-e543fb442d93
-- title:
--   Lemma 3.2 — incidence: with probability ≥ 1 − n^{−3}, every connected variable set U has I(U) < C_INC|U| + 4 ln n
-- statement:
--   For every $k\ge2$ and $m\ge0$, with $C_{\mathrm{INC}}=100k^2\lambda$, $\lambda=1+m/n$, a random formula $\Phi\sim\Phi(k,n,m)$ satisfies, with probability at least $1-n^{-3}$: every connected variable subset $U$ (i.e. $G_\Phi[U]$ connected) has
--   $$I(U)<C_{\mathrm{INC}}|U|+4\ln n,$$
--   where $I(U)$ is the number of clause labels meeting $U$. It bounds the number of clauses touching any connected piece of the formula.
--
--   Differences from the source:
--   - encoding: n variables (n ≥ 1 implicit) → hypothesis 1 ≤ n; reason: for n = 0 and m ≥ 1 the occurrence model has no formula (Fin 0 has no variable), so the probability is undefined; the hypothesis excludes only this undefined case
-- source:
--   He, Li, Yang, Fast Almost-Uniform Sampling of Random k-SAT Solutions, arXiv:2610.10474 (version not printed; file sha256 563a4d84…), p. 12, Lemma 3.2

import Mathlib
import Definitions.Def_RandKSATSample_Main_Formula
import Definitions.Def_RandKSATSample_Main_Structure

set_option autoImplicit false

namespace RandKSATSample.Main

/-- Lemma 3.2: for every `k ≥ 2` and `m ≥ 0`, with probability at least `1 − n^{−3}` every
connected variable set `U` satisfies `I(U) < C_INC |U| + 4 ln n`. -/
theorem lemma_3_2 (n m k : ℕ) (hn : 1 ≤ n) (hk : 2 ≤ k) :
    1 - (n : ℝ) ^ (-3 : ℤ) ≤ probF n m k (fun Φ => Incidence Φ) := by sorry

end RandKSATSample.Main
