-- Prove2me | Theorems.Thm_TTTSampling_lemma_3_9
-- name    : TTTSampling.lemma_3_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:42:35.612969+00:00
-- url     : https://prove2.me/theorems/e35db26e-33f3-4139-a2b9-21fe33fbc674
-- title:
--   Lemma 3.9 — almost surely $J\le 2\bar R\log_2|\mathcal F|+N$
-- statement:
--   Let $n\ge1$, $\mathcal F$ a finite class with $|\mathcal F|\ge2$, $\mu^\star\in\mathcal F$, $\hat\mu$ an oracle satisfying Assumption 3.1 with parameter $R\ge1$ and $\hat\mu(\emptyset)=1$, $\delta\in(0,1)$ and $C_{\mathsf N}\in\mathbb N$. Let $J$ be the number of iterations of the while loop of one round of Algorithm 3, the smallest $j$ such that every element of $\mathcal S^j$ has length $n$. Then with probability one
--
--   $$
--   J\;\le\;2\bar R\log_2|\mathcal F|+N.
--   $$
--
--   Each iteration either completes one particle or returns an incomplete one, and the latter halves the class (Lemma 3.6); this bound is the deterministic horizon used by the martingale arguments of Lemmas 3.13 and 3.15.
--
--   **Formalization Note** Stated for every path of positive probability of the loop run for $L\ge2\bar R\log_2|\mathcal F|+N$ iterations; the conclusion includes that a terminal state occurs on the path.
--
--   Differences from the source:
--   - encoding: $n$ a positive integer, $\mathcal F$ finite (Algorithm 3's input) → $1\le n$ and $2\le|\mathcal F|$; reason: Line 4 queries strings of length $1$; at $|\mathcal F|=1$ the formula for $N$ contains $\log 0$; only excludes undefined cases
--   - reading: "We also adopt the convention that $\mu(\emptyset)=1$" (p.18) → hypothesis $\hat\mu(\emptyset)=1$; reason: the proofs of Lemmas 3.10 and 3.15 use $\hat\mu(\emptyset)=1$; read as part of the standing setup
--   - reading: Algorithm 3 ("lexicographically first", the while loop) → `alg3Step` with Mathlib's lexicographic order on lists; the loop run for $L=N+2\bar R(\lfloor\log_2|\mathcal F|\rfloor+1)$ iterations of a kernel that is the identity on terminal states; reason: by Lemma 3.9 the loop ends within $L$ iterations, so this is the paper's loop
--   - reading: Algorithm 2 (Line 11's "for some $y$"; "If $\xi=1$, add $w_{i,t}$ to $\mathcal T$; set $\mathcal G^{\mathrm{ret}}\leftarrow\dots$") → `alg2`: the least violating $y$ in the order of $\Sigma$; both actions under $\xi=1$; coins clamped to $[0,1]$; a trial with undefined $\bar\eta(\cdot\mid v)$ ends with nothing added; reason: the printed line leaves $y$ unspecified; clamping and the fallback act only on unreachable states
--   - encoding: "almost surely" / "on the event" → for every outcome of positive probability; reason: equivalent for a discrete distribution
-- source:
--   Golowich, Moitra, Rohatgi, The Power of Test-Time Training for Approximate Sampling, arXiv:2606.11437 (version of November 3, 2026), Lemma 3.9, p.26 (PDF p.28)

import Mathlib
import Definitions.Def_TTTSampling_Assumption31
import Definitions.Def_TTTSampling_tvDist
import Definitions.Def_TTTSampling_alg3Path

namespace TTTSampling

/-- **Lemma 3.9.** With probability 1, we have `J ≤ 2R̄ · log₂ |ℱ| + N`.

Golowich, Moitra, Rohatgi, arXiv:2606.11437 (version of November 3, 2026), Lemma 3.9, printed
p.26 (PDF p.28). `J` is "the smallest index such that every element of 𝒮^J has length n".

**Formalization Note**
* Stated for every path of positive probability of the inner loop (`alg3Path`, which runs
  `pathLen ≥ 2R̄ log₂ |ℱ| + N` iterations); the conclusion includes that a terminal state occurs on
  the path.
* Standing data of §3.2 (Algorithm 3's input): `n ≥ 1`, `|ℱ| ≥ 2` (so that `N` is defined),
  `µ⋆ ∈ ℱ`, Assumption 3.1, the convention `µ̂(∅) = 1`, `R ≥ 1`, `δ ∈ (0,1)`, any `C_N`. -/
theorem lemma_3_9 (C_N : ℕ) {α : Type} [Fintype α] [LinearOrder α] {n : ℕ}
    (F : Finset (PMF (Fin n → α))) (R δ : ℝ) (μh : List α → NNReal) (μs : PMF (Fin n → α))
    (hn : 1 ≤ n) (hF : 2 ≤ F.card) (hμs : μs ∈ F) (hA : Assumption31 μs μh R)
    (h0 : μh [] = 1) (hR : 1 ≤ R) (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∀ p ∈ (alg3Path C_N R δ F μh).support, stopIdx p < p.length ∧
      (stopIdx p : ℝ) ≤ 2 * (Rbar R : ℝ) * Real.logb 2 F.card + Npart C_N F.card R δ := by sorry

end TTTSampling
