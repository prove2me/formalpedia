-- Prove2me | Theorems.Thm_SuttonTD_Convergence_ideal_prediction_eq
-- name    : SuttonTD.Convergence.ideal_prediction_eq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T06:23:48.558977+00:00
-- url     : https://prove2.me/theorems/605d5b46-4841-4d2e-ae1f-8a2a34adeb7e
-- title:
--   (5) — the ideal predictions $E\{z\mid i\}=[\sum_k Q^kh]_i=[(I-Q)^{-1}h]_i$
-- statement:
--   Let $C$ be an absorbing Markov chain with nonterminal block $Q$, and let $\bar z_j$ ($j\in T$) be expected outcomes, $[h]_i=\sum_{j\in T}p_{ij}\bar z_j$. The ideal prediction for the nonterminal state $i$ is the expected outcome
--
--   $$E\{z\mid i\}=\sum_{j\in T}p_{ij}\bar z_j+\sum_{j\in N}p_{ij}\sum_{k\in T}p_{jk}\bar z_k+\cdots=\Bigl[\sum_{k=0}^{\infty}Q^kh\Bigr]_i .$$
--
--   For every $i\in N$ this series converges, and
--
--   $$\Bigl[\sum_{k=0}^{\infty}Q^kh\Bigr]_i=\bigl[(I-Q)^{-1}h\bigr]_i .$$
--
--   This identifies the target of Theorem 2.
-- source:
--   Sutton (1988), Machine Learning 3:9–44, §4.1, (5), p. 24 (PDF p. 16)

import Definitions.Def_SuttonTD_Convergence_AbsorbingChain
open Matrix

namespace SuttonTD.Convergence

/-- **The ideal predictions (5)** (Sutton 1988, §4.1, p. 24, PDF p. 16): for an absorbing Markov
chain with nonterminal block `Q` and `[h]_i = ∑_{j ∈ T} p_ij z̄_j`,
`E{z | i} = [∑_{k=0}^∞ Qᵏ h]_i = [(I − Q)⁻¹ h]_i` for every `i ∈ N`: the series converges and its
sum is the `i`-th component of `(I − Q)⁻¹ h`.

Formalization Note: `E{z | i}` is the paper's expansion
`∑_{j∈T} p_ij z̄_j + ∑_{j∈N} p_ij ∑_{k∈T} p_jk z̄_k + ⋯ = [∑_k Qᵏh]_i` (p. 24); the statement is
the convergence of that series and the second equality of (5). `z̄ : T → ℝ` is arbitrary. -/
theorem ideal_prediction_eq {N T : Type*} [Fintype N] [DecidableEq N] [Fintype T]
    (C : AbsorbingChain N T) (zbar : T → ℝ) (i : N) :
    HasSum (fun k : ℕ => (C.Q ^ k *ᵥ C.h zbar) i) (((1 - C.Q)⁻¹ *ᵥ C.h zbar) i) := by sorry

end SuttonTD.Convergence
