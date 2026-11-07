-- Prove2me | Theorems.Thm_TTTSampling_lemma_3_15
-- name    : TTTSampling.lemma_3_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:43:14.182406+00:00
-- url     : https://prove2.me/theorems/dd787b06-86b1-492c-a433-83b64d8a988c
-- title:
--   Lemma 3.15 (corrected: $\delta\in(0,1/2)$) — Algorithm 3 makes $O(n|\Sigma|R^{12}\sqrt{\log|\mathcal F|}\log\frac1\delta\log\frac{R\log|\mathcal F|}\delta)$ oracle calls w.p. $1-\delta$
-- statement:
--   There is an absolute constant $C_0$ such that for every $C_{\mathsf N}\ge C_0$ there is $C>0$ with the following property. Let $n\ge1$, $|\mathcal F|\ge2$, $\mu^\star\in\mathcal F$, $\hat\mu$ satisfying Assumption 3.1 with parameter $R\ge1$ and $\hat\mu(\emptyset)=1$, $\delta\in(0,1/2)$ and $x_0\in\Sigma^n$. Let $Q$ be the number of oracle calls made by Algorithm 3 with parameters $C_{\mathsf N}$, $R$, $\delta$. Then each of the following holds with probability at least $1-\delta$:
--
--   $$
--   Q\le C\, n\,|\Sigma|\,K\,R\bar R^2\Bigl\lceil\sqrt{\log|\mathcal F|}\,R^2\bar R^2\Bigl(\log\frac{R\log|\mathcal F|}{\delta}\Bigr)\Bigr\rceil,
--   \qquad
--   Q\le C\, n\,|\Sigma|\,R^{12}\sqrt{\log|\mathcal F|}\,\log\frac1\delta\,\log\frac{R\log|\mathcal F|}{\delta}.
--   $$
--
--   Oracle calls are counted with caching across all calls of Algorithms 2 and 3. Together with Lemma 3.14 this gives Theorem 3.2 after truncating the rare expensive runs.
--
--   Differences from the source:
--   - correction: the lemma for every $\delta\in(0,1)$ (no range stated; Algorithm 3 allows $\delta\in(0,1)$) → $\delta\in(0,1/2)$; reason: false as printed: $n=1$, $\Sigma=\{0,1\}$, $R=1$, $\hat\mu=\mu^\star$; every run makes $|\Sigma|=2$ calls (Line 4), while the second bound tends to $0$ as $\delta\to1$ for $|\mathcal F|=3$ and the first is negative for $|\mathcal F|=2$, $\delta\ge0.7$; $(0,1/2)$ is the range of Lemma 3.14 and the only one the proof of Theorem 3.2 uses
--   - reading: "for an appropriate constant $C_{\mathsf N}$" and $O(\cdot)$ → $\exists C_0\,\forall C_{\mathsf N}\ge C_0\,\exists C>0$, $C$ before all other parameters; reason: the first bound omits $C_{\mathsf N}$, so its constant absorbs it; the proofs increase $C_{\mathsf N}$ as needed
--   - encoding: the chain of two $O(\cdot)$ bounds "with probability $1-\delta$" → both bounds, each with probability at least $1-\delta$; reason: the displayed equality of the two $O(\cdot)$ is the claim that both hold
--   - encoding: "the number of oracle calls to $\hat\mu$" → the number of distinct nodes read over the run (cache across rounds), the empty sequence excepted; reason: caching paragraph p.18 and "$\hat\mu(\emptyset)=1$ is fixed by convention", proof p.30
--   - encoding: $n$ a positive integer, $\mathcal F$ finite (Algorithm 3's input) → $1\le n$ and $2\le|\mathcal F|$; reason: Line 4 queries strings of length $1$; at $|\mathcal F|=1$ the formula for $N$ contains $\log 0$; only excludes undefined cases
--   - reading: "We also adopt the convention that $\mu(\emptyset)=1$" (p.18) → hypothesis $\hat\mu(\emptyset)=1$; reason: the proofs of Lemmas 3.10 and 3.15 use $\hat\mu(\emptyset)=1$; read as part of the standing setup
--   - reading: Algorithm 3 ("lexicographically first", the while loop) → `alg3Step` with Mathlib's lexicographic order on lists; the loop run for $L=N+2\bar R(\lfloor\log_2|\mathcal F|\rfloor+1)$ iterations of a kernel that is the identity on terminal states; reason: by Lemma 3.9 the loop ends within $L$ iterations, so this is the paper's loop
--   - reading: Algorithm 2 (Line 11's "for some $y$"; "If $\xi=1$, add $w_{i,t}$ to $\mathcal T$; set $\mathcal G^{\mathrm{ret}}\leftarrow\dots$") → `alg2`: the least violating $y$ in the order of $\Sigma$; both actions under $\xi=1$; coins clamped to $[0,1]$; a trial with undefined $\bar\eta(\cdot\mid v)$ ends with nothing added; reason: the printed line leaves $y$ unspecified; clamping and the fallback act only on unreachable states
-- source:
--   Golowich, Moitra, Rohatgi, The Power of Test-Time Training for Approximate Sampling, arXiv:2606.11437 (version of November 3, 2026), Lemma 3.15, p.30 (PDF p.32)

import Mathlib
import Definitions.Def_TTTSampling_Assumption31
import Definitions.Def_TTTSampling_tvDist
import Definitions.Def_TTTSampling_qBound
import Definitions.Def_TTTSampling_alg3

namespace TTTSampling

/-- **Lemma 3.15** (corrected: `δ ∈ (0, 1/2)`). The number of oracle calls to `µ̂` made by
Algorithm 3 is upper bounded by
`O(n·|Σ|·K·RR̄²·⌈√(log |ℱ|)·R²R̄²(log(R log |ℱ|/δ))⌉) = O(n·|Σ|·R¹²·√(log |ℱ|)·log(1/δ)·log(R log |ℱ|/δ))`
with probability `1 − δ`.

Golowich, Moitra, Rohatgi, arXiv:2606.11437 (version of November 3, 2026), Lemma 3.15, printed
p.30 (PDF p.32).

**Formalization Note**
* "For an appropriate constant `C_N`": there is an absolute `C₀` such that the lemma holds for
  every `C_N ≥ C₀`; the constant `C` of the `O(·)` is chosen after `C_N` (the first bound omits
  `C_N`, so its constant absorbs it) and before all other parameters.
* Both displayed bounds are stated, each with probability at least `1 − δ`.
* The count is the number of distinct nodes evaluated, with caching across all calls (p.18).
* **Correction.** As printed (`δ ∈ (0,1)`, Algorithm 3's range) the lemma is false: with
  `n = 1`, `Σ = {0,1}`, `R = 1`, `µ̂ = µ⋆`, every run makes `|Σ| = 2` queries (Line 4), while
  the second bound tends to `0` as `δ → 1` (`|ℱ| = 3`) and the first is negative for `|ℱ| = 2`,
  `δ ≥ 0.7`. It is stated for `δ ∈ (0, 1/2)`, the range of Lemma 3.14 and the only one the proof
  of Theorem 3.2 uses (`δ/2`).
* Standing data as in Lemma 3.9. -/
theorem lemma_3_15 :
    ∃ C₀ : ℕ, ∀ C_N : ℕ, C₀ ≤ C_N → ∃ C : ℝ, 0 < C ∧
      ∀ {α : Type} [Fintype α] [LinearOrder α] {n : ℕ} (F : Finset (PMF (Fin n → α)))
        (R δ : ℝ) (μh : List α → NNReal) (μs : PMF (Fin n → α)) (x₀ : Fin n → α),
        1 ≤ n → 2 ≤ F.card → μs ∈ F → Assumption31 μs μh R → μh [] = 1 → 1 ≤ R →
        0 < δ → δ < 1 / 2 →
        1 - δ ≤ prob (alg3 C_N R δ F μh x₀) (fun r =>
            (r.2 : ℝ) ≤ C * n * Fintype.card α * Kreps R δ * R * (Rbar R : ℝ) ^ 2 *
              ⌈Real.sqrt (Real.log F.card) * R ^ 2 * (Rbar R : ℝ) ^ 2 *
                Real.log (R * Real.log F.card / δ)⌉₊) ∧
        1 - δ ≤ prob (alg3 C_N R δ F μh x₀) (fun r =>
            (r.2 : ℝ) ≤ C * qBound n (Fintype.card α) R F.card δ) := by sorry

end TTTSampling
