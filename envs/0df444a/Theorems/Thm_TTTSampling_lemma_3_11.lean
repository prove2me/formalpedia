-- Prove2me | Theorems.Thm_TTTSampling_lemma_3_11
-- name    : TTTSampling.lemma_3_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:42:20.283574+00:00
-- url     : https://prove2.me/theorems/17f6bcd5-fc02-42e6-a07b-c6ac92674661
-- title:
--   Lemma 3.11 (Unbiasedness) — $\mathbb E[\mathrm{occ}(x,\mathcal S^{\mathrm{term}})]=N\mu^\star(x)$
-- statement:
--   Under the hypotheses of Lemma 3.9, for every $x\in\Sigma^n$,
--
--   $$
--   \mathbb E\bigl[\mathrm{occ}(x,\mathcal S^{\mathrm{term}})\bigr]=N\cdot\mu^\star(x),
--   $$
--
--   where $\mathcal S^{\mathrm{term}}=\mathcal S^J$ is the terminal multiset of one round of Algorithm 3, $\mathrm{occ}(x,\mathcal S)$ is the multiplicity of $x$ in $\mathcal S$, and the expectation is over the randomness of Algorithm 3.
--
--   Each terminal particle is therefore an unbiased importance-weighted sample of $\mu^\star$; the final rejection step of Line 13 turns this into an approximate sample (Lemma 3.14).
--
--   **Formalization Note** The expectation is over one round; all rounds have the same law of particles.
--
--   Differences from the source:
--   - encoding: $n$ a positive integer, $\mathcal F$ finite (Algorithm 3's input) → $1\le n$ and $2\le|\mathcal F|$; reason: Line 4 queries strings of length $1$; at $|\mathcal F|=1$ the formula for $N$ contains $\log 0$; only excludes undefined cases
--   - reading: "We also adopt the convention that $\mu(\emptyset)=1$" (p.18) → hypothesis $\hat\mu(\emptyset)=1$; reason: the proofs of Lemmas 3.10 and 3.15 use $\hat\mu(\emptyset)=1$; read as part of the standing setup
--   - reading: Algorithm 3 ("lexicographically first", the while loop) → `alg3Step` with Mathlib's lexicographic order on lists; the loop run for $L=N+2\bar R(\lfloor\log_2|\mathcal F|\rfloor+1)$ iterations of a kernel that is the identity on terminal states; reason: by Lemma 3.9 the loop ends within $L$ iterations, so this is the paper's loop
--   - reading: Algorithm 2 (Line 11's "for some $y$"; "If $\xi=1$, add $w_{i,t}$ to $\mathcal T$; set $\mathcal G^{\mathrm{ret}}\leftarrow\dots$") → `alg2`: the least violating $y$ in the order of $\Sigma$; both actions under $\xi=1$; coins clamped to $[0,1]$; a trial with undefined $\bar\eta(\cdot\mid v)$ ends with nothing added; reason: the printed line leaves $y$ unspecified; clamping and the fallback act only on unreachable states
-- source:
--   Golowich, Moitra, Rohatgi, The Power of Test-Time Training for Approximate Sampling, arXiv:2606.11437 (version of November 3, 2026), Lemma 3.11, p.27 (PDF p.29)

import Mathlib
import Definitions.Def_TTTSampling_Assumption31
import Definitions.Def_TTTSampling_tvDist
import Definitions.Def_TTTSampling_alg3Path

namespace TTTSampling

/-- **Lemma 3.11 (Unbiasedness).** For each `x ∈ Σⁿ`, it holds that
`𝔼[occ(x, 𝒮^term)] = N · µ⋆(x)`, where the expectation is over the randomness in Algorithm 3.

Golowich, Moitra, Rohatgi, arXiv:2606.11437 (version of November 3, 2026), Lemma 3.11, printed
p.27 (PDF p.29). `𝒮^term = 𝒮^J` (Algorithm 3, Line 12).

**Formalization Note** The expectation is over one round of Algorithm 3 (the law of `𝒮^term` is
the same in every round). `occ(x, 𝒮)` is the multiplicity of `x` in the multiset `𝒮`. Standing
data as in Lemma 3.9. -/
theorem lemma_3_11 (C_N : ℕ) {α : Type} [Fintype α] [LinearOrder α] {n : ℕ}
    (F : Finset (PMF (Fin n → α))) (R δ : ℝ) (μh : List α → NNReal) (μs : PMF (Fin n → α))
    (hn : 1 ≤ n) (hF : 2 ≤ F.card) (hμs : μs ∈ F) (hA : Assumption31 μs μh R)
    (h0 : μh [] = 1) (hR : 1 ≤ R) (hδ : 0 < δ) (hδ1 : δ < 1) (x : Fin n → α) :
    expect (alg3Path C_N R δ F μh)
        (fun p => ((sAt p (stopIdx p)).count (List.ofFn x) : ℝ)) =
      (Npart C_N F.card R δ : ℝ) * (μs x).toReal := by sorry

end TTTSampling
