-- Prove2me | Theorems.Thm_SennottDP_Tauberian_block_example
-- name    : SennottDP.Tauberian.block_example
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T13:34:24.701762+00:00
-- url     : https://prove2.me/theorems/a3eb46cc-b320-4956-ad86-f75c6d4ace41
-- title:
--   Example A.5.1 — a 0/1 block sequence with liminf w_n/n = 1/2 and limsup 2/3 (or 1)
-- statement:
--   Let $(u_n)_{n\ge 0}$ be the 0/1 block sequence built from positive integers $(q_k)_{k\ge1}$ ($q_1$ ones, $q_1$ zeros, $q_2$ ones, $q_2$ zeros, …), let $s_k = \sum_{i=1}^k q_i$ and $w_n = \sum_{k=0}^{n-1} u_k$. Then:
--
--   1. for every sequence of positive integers $(q_k)$, $\liminf_{n\to\infty} w_n/n = \tfrac12$;
--   2. for $q_k \equiv q$ (a positive constant) and for $q_k = k$, $\lim_{n\to\infty} w_n/n = \tfrac12$;
--   3. for Choice One, $q_1 = 1$ and $q_{k+1} = s_k$, $\limsup_{n\to\infty} w_n/n = \tfrac23$;
--   4. for Choice Two, $q_1 = 1$ and $q_{k+1} = (k+1)s_k$, $\limsup_{n\to\infty} w_n/n = 1$;
--   5. for Choice One and for Choice Two, the middle inequality in (A.28) is strict:
--   $$\liminf_{\alpha\to1^-}(1-\alpha)U(\alpha) < \limsup_{\alpha\to1^-}(1-\alpha)U(\alpha).$$
--
--   The example shows that the Cesàro and Abel means of a bounded nonnegative sequence need not converge, and that some inequalities of (A.28) can be strict.
--
--   **Formalization Note** Items 3 and 4 quantify over every $q : \mathbb{N} \to \mathbb{N}$ satisfying the recursion for $k \ge 1$ (the value $q_0$ is unused), which determines $q_k$ for $k \ge 1$.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), pp. 286–287, Example A.5.1, (A.42), Fig. A.4

import Mathlib
import Definitions.Def_SennottDP_Tauberian_PowerSeries
import Definitions.Def_SennottDP_Tauberian_BlockSequence

open scoped ENNReal NNReal Topology
open Filter

namespace SennottDP.Tauberian

/-- Sennott (1999), pp. 286–287, Example A.5.1, for the 0/1 block sequence `u` of Fig. A.4
(`q_1` ones, `q_1` zeros, `q_2` ones, `q_2` zeros, …; `s_k = ∑_{i ≤ k} q_i`):
1. for every sequence of positive integers `(q_k)_{k ≥ 1}`, `lim inf_n w_n/n = 1/2`;
2. for `q_k ≡ q` (a positive constant) and for `q_k = k`, `lim_n w_n/n = 1/2`;
3. Choice One (`q_1 = 1`, `q_{k+1} = s_k`): `lim sup_n w_n/n = 2/3`;
4. Choice Two (`q_1 = 1`, `q_{k+1} = (k+1) s_k`): `lim sup_n w_n/n = 1`;
5. in either choice the middle inequality in (A.28) is strict. -/
theorem block_example :
    (∀ q : ℕ → ℕ, (∀ k, 1 ≤ k → 0 < q k) →
        liminf (cesaroMean (blockSeq q)) atTop = 1 / 2) ∧
    (∀ (q : ℕ → ℕ) (c : ℕ), 0 < c → (∀ k, 1 ≤ k → q k = c) →
        Tendsto (cesaroMean (blockSeq q)) atTop (𝓝 (1 / 2))) ∧
    (∀ q : ℕ → ℕ, (∀ k, 1 ≤ k → q k = k) →
        Tendsto (cesaroMean (blockSeq q)) atTop (𝓝 (1 / 2))) ∧
    (∀ q : ℕ → ℕ, q 1 = 1 → (∀ k, 1 ≤ k → q (k + 1) = blockSum q k) →
        limsup (cesaroMean (blockSeq q)) atTop = 2 / 3 ∧
          liminf (abelMean (blockSeq q)) (𝓝[<] (1 : ℝ≥0))
            < limsup (abelMean (blockSeq q)) (𝓝[<] (1 : ℝ≥0))) ∧
    (∀ q : ℕ → ℕ, q 1 = 1 → (∀ k, 1 ≤ k → q (k + 1) = (k + 1) * blockSum q k) →
        limsup (cesaroMean (blockSeq q)) atTop = 1 ∧
          liminf (abelMean (blockSeq q)) (𝓝[<] (1 : ℝ≥0))
            < limsup (abelMean (blockSeq q)) (𝓝[<] (1 : ℝ≥0))) := by sorry

end SennottDP.Tauberian
