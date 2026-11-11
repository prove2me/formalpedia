-- Prove2me | Theorems.Thm_PostedPriceLimits_FullRevelation_lemma_5_1
-- name    : PostedPriceLimits.FullRevelation.lemma_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:41:18.672928+00:00
-- url     : https://prove2.me/theorems/2bd54bcb-fbf8-4164-a705-6ed0a170df78
-- title:
--   Lemma 5.1 — $\vartheta_{t,k,I}\ge1/\sqrt{\mathrm{val}(k)}$
-- statement:
--   In the construction of §5 (for all sufficiently large $n$), let $Z_{t,k,I}=\bigcap_{\gamma\subseteq\tau_t(I)}\{x\in Z_t:\psi'_{t,\gamma}(x)\ge\varphi_{|\gamma|}(k)\}$ and $\vartheta_{t,k,I}=\Pr[x\in Z_{t,k,I}]$ for an item $x$ of block $Z_t$. Then for every block $t$, every $I\subseteq[n]$ and every $k\in[\kappa]$,
--   $$\vartheta_{t,k,I}\ge\frac1{\sqrt{\mathrm{val}(k)}}.$$
--
--   This makes the conditional owner-rank probabilities $\mathbf 1(x\in Z_{t,k,[n]})/(\vartheta_{t,k,[n]}\mathrm{val}(k))$ sum to at most $1$, so the owner valuation is well defined, and it gives the size bound of Proposition A.2-(2).
--
--   **Formalization Note** "For sufficiently large $n$" (the standing assumption of §5) is $\exists N\,\forall n\ge N$ with $N$ absolute. The probability is taken under the full law of the randomness and recorded for every item $x$.
--
--   Differences from the source:
--   - encoding: bidders and blocks indexed 1..n; [i−1] = bidders visited before i, [i] = bidders up to i → bidders and blocks are Fin n = {0,…,n−1}; [i−1] ↦ before i = {j | j < i}, [i] ↦ upTo i = {j | j ≤ i}; reason: 0-based indexing of the same objects; no instance changes
--   - encoding: π, τ_t, N_{t,i}, ψ_{t,γ}, ξ_{t,γ} and the owner-rank draws sampled as described on printed pp.15–17 → the same objects as deterministic functions of independent Unif[0,1] labels (inversion for ψ, ξ = 2U, coin U < 1/m, rank by cumulative intervals) together with uniform injections τ_t and a uniform permutation π; reason: a coupling with exactly the source's joint law of all objects the statements mention; the mechanism never sees the raw labels
--   - encoding: ϑ_{t,k,I} = Pr[x ∈ Z_{t,k,I}] for some fixed x ∈ Z_t → theta n t k I x for every item x; reason: the probability does not depend on x; stating it for all x includes the fixed one
-- source:
--   Frederick Qiu, Aviad Rubinstein, STOC 2027 submission #1596 (October 2026), Lemma 5.1, p.16 (PDF 17); PDF SHA-256 5be77a250fd554b42d30cff15c46dafe3e43c75a2d90968fae98c61ff1113bb3; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1596.pdf

import Mathlib
import Definitions.Def_PostedPriceLimits_FullRevelation_Construction

namespace PostedPriceLimits.FullRevelation

/-- Lemma 5.1 (for all sufficiently large `n`). `ϑ_{t,k,I} ≥ 1/√val(k)` for all `I ⊆ [n]` and
`k ∈ [κ]`. -/
theorem lemma_5_1 : ∃ N : ℕ, ∀ n ≥ N, ∀ (t : Fin n) (k : ℕ), k ∈ rankRange (kappa n) →
    ∀ (I : Finset (Fin n)) (x : Fin (blockSize n)),
      1 / Real.sqrt (val n k) ≤ theta n t k I x := by sorry

end PostedPriceLimits.FullRevelation
