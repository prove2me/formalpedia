-- Prove2me | Theorems.Thm_TTTSampling_lemma_3_13
-- name    : TTTSampling.lemma_3_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:42:46.295517+00:00
-- url     : https://prove2.me/theorems/34793f31-2bb0-498b-85d9-214af75f52dd
-- title:
--   Lemma 3.13 — concentration of $M_j$: $\max_{j\le J}|M_j-M_0|\le M_0/2$ w.p. $\ge1-\delta/(2R)$ and $\mathbb E[(M_J/(2RN)-1)_+]\le\delta/(2R)$
-- statement:
--   There is an absolute constant $C_0$ such that for every $C_{\mathsf N}\ge C_0$ the following holds. Let $n\ge1$, $|\mathcal F|\ge2$, $\mu^\star\in\mathcal F$, $\hat\mu$ satisfying Assumption 3.1 with parameter $R\ge1$ and $\hat\mu(\emptyset)=1$, and $\delta\in(0,1)$. Along the inner loop of one round of Algorithm 3 (with parameters $C_{\mathsf N}$, $R$, $\delta$), with $M_j=\sum_{x\in\mathcal S^j}\mu^\star(x)/\hat\mu(x)$,
--
--   $$
--   \mathbb P\Bigl(\max_{1\le j\le J}|M_j-M_0|\le\frac{M_0}2\Bigr)\ge1-\frac{\delta}{2R},\qquad
--   \mathbb E\Bigl[\Bigl(\frac{M_J}{2RN}-1\Bigr)_+\Bigr]\le\frac{\delta}{2R}.
--   $$
--
--   This is where $\sqrt{\log|\mathcal F|}$ enters: the martingale has $O(\bar R\log|\mathcal F|+N)$ steps of size $O(R\bar R)$, so $N\gtrsim\sqrt{\log|\mathcal F|}\,\mathrm{poly}(R)$ particles suffice for its fluctuations to be a small fraction of $M_0=N$.
--
--   **Formalization Note** The maximum is the event "for all $1\le j\le J$"; $(a)_+=\max(0,a)$.
--
--   Differences from the source:
--   - reading: "for an appropriate constant $C_{\mathsf N}$, specified in Lemma 3.13" → there is an absolute $C_0$ such that the statement holds for every $C_{\mathsf N}\ge C_0$; reason: the proofs choose $C_{\mathsf N}$ "after increasing $C_{\mathsf N}$ if necessary"; this is the stronger of the two readings
--   - encoding: $\max_{1\le j\le J}|M_j-M_0|\le M_0/2$ → $|M_j-M_0|\le M_0/2$ for all $1\le j\le J$; reason: same event
--   - encoding: $N=C_{\mathsf N}\lceil x\rceil$ with $x=\sqrt{\log|\mathcal F|}R^2\bar R^2\log(R\log|\mathcal F|/\delta)$, undefined as a particle count when $x\le0$ (possible for $|\mathcal F|=2$, $R\log2\le\delta$) → $\lceil x\rceil=0$, so $N=0$ and both claims hold trivially (no particles; $M_J/(2RN)$ is $0$); reason: only affects inputs where the printed $N$ is not a positive count
--   - encoding: $n$ a positive integer, $\mathcal F$ finite (Algorithm 3's input) → $1\le n$ and $2\le|\mathcal F|$; reason: Line 4 queries strings of length $1$; at $|\mathcal F|=1$ the formula for $N$ contains $\log 0$; only excludes undefined cases
--   - reading: "We also adopt the convention that $\mu(\emptyset)=1$" (p.18) → hypothesis $\hat\mu(\emptyset)=1$; reason: the proofs of Lemmas 3.10 and 3.15 use $\hat\mu(\emptyset)=1$; read as part of the standing setup
--   - reading: Algorithm 3 ("lexicographically first", the while loop) → `alg3Step` with Mathlib's lexicographic order on lists; the loop run for $L=N+2\bar R(\lfloor\log_2|\mathcal F|\rfloor+1)$ iterations of a kernel that is the identity on terminal states; reason: by Lemma 3.9 the loop ends within $L$ iterations, so this is the paper's loop
--   - reading: Algorithm 2 (Line 11's "for some $y$"; "If $\xi=1$, add $w_{i,t}$ to $\mathcal T$; set $\mathcal G^{\mathrm{ret}}\leftarrow\dots$") → `alg2`: the least violating $y$ in the order of $\Sigma$; both actions under $\xi=1$; coins clamped to $[0,1]$; a trial with undefined $\bar\eta(\cdot\mid v)$ ends with nothing added; reason: the printed line leaves $y$ unspecified; clamping and the fallback act only on unreachable states
-- source:
--   Golowich, Moitra, Rohatgi, The Power of Test-Time Training for Approximate Sampling, arXiv:2606.11437 (version of November 3, 2026), Lemma 3.13, p.28 (PDF p.30)

import Mathlib
import Definitions.Def_TTTSampling_Assumption31
import Definitions.Def_TTTSampling_tvDist
import Definitions.Def_TTTSampling_alg3Path

namespace TTTSampling

/-- **Lemma 3.13.** Fix any `δ ∈ (0, 1)`. Then the martingale `(M_j)_{j≥0}` satisfies
`ℙ(max_{1≤j≤J} |M_j − M_0| ≤ M_0/2) ≥ 1 − δ/(2R)` and `𝔼[(M_J/(2RN) − 1)₊] ≤ δ/(2R)`.

Golowich, Moitra, Rohatgi, arXiv:2606.11437 (version of November 3, 2026), Lemma 3.13, printed
p.28 (PDF p.30); `C_N` is "an appropriate constant … specified in Lemma 3.13" (Algorithm 3, Line 1).

**Formalization Note**
* "For an appropriate constant `C_N`" is read as: there is an absolute `C₀` such that the lemma
  holds for every `C_N ≥ C₀` (the proofs' "after increasing `C_N` if necessary").
* The maximum over `1 ≤ j ≤ J` is the event "for all `1 ≤ j ≤ J`"; `(·)₊ = max 0 ·`.
* Standing data as in Lemma 3.9, with `δ ∈ (0,1)` as printed. -/
theorem lemma_3_13 :
    ∃ C₀ : ℕ, ∀ C_N : ℕ, C₀ ≤ C_N →
      ∀ {α : Type} [Fintype α] [LinearOrder α] {n : ℕ} (F : Finset (PMF (Fin n → α)))
        (R δ : ℝ) (μh : List α → NNReal) (μs : PMF (Fin n → α)),
        1 ≤ n → 2 ≤ F.card → μs ∈ F → Assumption31 μs μh R → μh [] = 1 → 1 ≤ R →
        0 < δ → δ < 1 →
        1 - δ / (2 * R) ≤ prob (alg3Path C_N R δ F μh) (fun p =>
            ∀ j : ℕ, 1 ≤ j → j ≤ stopIdx p →
              |Mval μs μh (sAt p j) - Mval μs μh (sAt p 0)| ≤ Mval μs μh (sAt p 0) / 2) ∧
        expect (alg3Path C_N R δ F μh) (fun p =>
            max 0 (Mval μs μh (sAt p (stopIdx p)) / (2 * R * (Npart C_N F.card R δ : ℝ)) - 1)) ≤
          δ / (2 * R) := by sorry

end TTTSampling
