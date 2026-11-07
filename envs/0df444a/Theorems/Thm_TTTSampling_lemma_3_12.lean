-- Prove2me | Theorems.Thm_TTTSampling_lemma_3_12
-- name    : TTTSampling.lemma_3_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:42:37.136634+00:00
-- url     : https://prove2.me/theorems/60ffeaf8-d01b-43a9-ae15-44dd429f9647
-- title:
--   Lemma 3.12 — $M_j=\sum_{x\in\mathcal S^j}\mu^\star(x)/\hat\mu(x)$ is a martingale
-- statement:
--   Under the hypotheses of Lemma 3.9, let $M_j=\sum_{x\in\mathcal S^j}\mu^\star(x)/\hat\mu(x)$ (with multiplicity) along the inner loop of one round of Algorithm 3. Then $(M_j)_{j\ge0}$ is a martingale with respect to the filtration $(\mathscr F^j)_{j\ge0}$: for every $j\ge1$,
--
--   $$
--   \mathbb E\bigl[M_j\mid\mathscr F^{j-1}\bigr]=M_{j-1}.
--   $$
--
--   At termination $M_J=|\mathcal S^{\mathrm{term}}|$ (since $\hat\mu=\mu^\star$ on $\Sigma^n$), so the concentration of this martingale (Lemma 3.13) controls the truncation of the final rejection step.
--
--   Differences from the source:
--   - encoding: martingale with respect to the filtration $(\mathscr F^j)$ of all random variables up to iteration $j$ → one-step identity $\mathbb E[\,\cdot\,(\text{next state})\mid\text{state }j]=\,\cdot\,(\text{state }j)$ at every state of a path of positive probability, the transition being `alg3Step`; reason: the inner loop is a Markov chain on (particles, class, cache) driven by fresh randomness, so the two statements are the same
--   - encoding: $n$ a positive integer, $\mathcal F$ finite (Algorithm 3's input) → $1\le n$ and $2\le|\mathcal F|$; reason: Line 4 queries strings of length $1$; at $|\mathcal F|=1$ the formula for $N$ contains $\log 0$; only excludes undefined cases
--   - reading: "We also adopt the convention that $\mu(\emptyset)=1$" (p.18) → hypothesis $\hat\mu(\emptyset)=1$; reason: the proofs of Lemmas 3.10 and 3.15 use $\hat\mu(\emptyset)=1$; read as part of the standing setup
--   - reading: Algorithm 3 ("lexicographically first", the while loop) → `alg3Step` with Mathlib's lexicographic order on lists; the loop run for $L=N+2\bar R(\lfloor\log_2|\mathcal F|\rfloor+1)$ iterations of a kernel that is the identity on terminal states; reason: by Lemma 3.9 the loop ends within $L$ iterations, so this is the paper's loop
--   - reading: Algorithm 2 (Line 11's "for some $y$"; "If $\xi=1$, add $w_{i,t}$ to $\mathcal T$; set $\mathcal G^{\mathrm{ret}}\leftarrow\dots$") → `alg2`: the least violating $y$ in the order of $\Sigma$; both actions under $\xi=1$; coins clamped to $[0,1]$; a trial with undefined $\bar\eta(\cdot\mid v)$ ends with nothing added; reason: the printed line leaves $y$ unspecified; clamping and the fallback act only on unreachable states
-- source:
--   Golowich, Moitra, Rohatgi, The Power of Test-Time Training for Approximate Sampling, arXiv:2606.11437 (version of November 3, 2026), Lemma 3.12, p.28 (PDF p.30)

import Mathlib
import Definitions.Def_TTTSampling_Assumption31
import Definitions.Def_TTTSampling_tvDist
import Definitions.Def_TTTSampling_alg3Path

namespace TTTSampling

/-- **Lemma 3.12.** `(M_j)_{j≥0}` is a martingale with respect to the filtration `(ℱ^j)_{j≥0}`,
i.e., for every `j ≥ 1` we have `𝔼[M_j | ℱ^{j−1}] = M_{j−1}`.

Golowich, Moitra, Rohatgi, arXiv:2606.11437 (version of November 3, 2026), Lemma 3.12, printed
p.28 (PDF p.30), with `M_j := Σ_{x∈𝒮^j} µ⋆(x)/µ̂(x)` (p.28).

**Formalization Note** As in Lemma 3.10, the conditional expectation given `ℱ^{j−1}` is the
expectation under the transition `alg3Step` from the state at index `j − 1`, at every state of a
path of positive probability. Standing data as in Lemma 3.9. -/
theorem lemma_3_12 (C_N : ℕ) {α : Type} [Fintype α] [LinearOrder α] {n : ℕ}
    (F : Finset (PMF (Fin n → α))) (R δ : ℝ) (μh : List α → NNReal) (μs : PMF (Fin n → α))
    (hn : 1 ≤ n) (hF : 2 ≤ F.card) (hμs : μs ∈ F) (hA : Assumption31 μs μh R)
    (h0 : μh [] = 1) (hR : 1 ≤ R) (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∀ p ∈ (alg3Path C_N R δ F μh).support, ∀ j : ℕ, j < pathLen C_N F.card R δ →
      expect (alg3Step R μh (stAt p j)) (fun s => Mval μs μh s.S) = Mval μs μh (sAt p j) := by sorry

end TTTSampling
