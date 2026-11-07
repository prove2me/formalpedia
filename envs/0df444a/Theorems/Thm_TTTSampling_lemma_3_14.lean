-- Prove2me | Theorems.Thm_TTTSampling_lemma_3_14
-- name    : TTTSampling.lemma_3_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:43:48.660196+00:00
-- url     : https://prove2.me/theorems/126aeeeb-8ce2-45fb-b9f5-756a50f00c29
-- title:
--   Lemma 3.14 — for $\delta\in(0,1/2)$, Algorithm 3 samples within total variation $\delta$ of $\mu^\star$
-- statement:
--   There is an absolute constant $C_0$ such that for every $C_{\mathsf N}\ge C_0$ the following holds. Let $n\ge1$, $|\mathcal F|\ge2$, $\mu^\star\in\mathcal F$, $\hat\mu$ satisfying Assumption 3.1 with parameter $R\ge1$ and $\hat\mu(\emptyset)=1$, $\delta\in(0,1/2)$, and $x_0\in\Sigma^n$ the fixed string of Line 14. Let $\mu^{\mathrm{alg}}$ be the output distribution of Algorithm 3 with parameters $C_{\mathsf N}$, $R$, $\delta$. Then
--
--   $$
--   D_{\mathrm{TV}}\bigl(\mu^\star,\mu^{\mathrm{alg}}\bigr)\le\delta.
--   $$
--
--   This is the correctness half of Theorem 3.2; the query-count half is Lemma 3.15.
--
--   Differences from the source:
--   - reading: "for an appropriate constant $C_{\mathsf N}$, specified in Lemma 3.13" → there is an absolute $C_0$ such that the statement holds for every $C_{\mathsf N}\ge C_0$; reason: the proofs choose $C_{\mathsf N}$ "after increasing $C_{\mathsf N}$ if necessary"; this is the stronger of the two readings
--   - encoding: "an arbitrary fixed element of $\Sigma^n$" (Line 14) → the statement holds for every choice $x_0$; reason: the element is arbitrary
--   - encoding: $n$ a positive integer, $\mathcal F$ finite (Algorithm 3's input) → $1\le n$ and $2\le|\mathcal F|$; reason: Line 4 queries strings of length $1$; at $|\mathcal F|=1$ the formula for $N$ contains $\log 0$; only excludes undefined cases
--   - reading: "We also adopt the convention that $\mu(\emptyset)=1$" (p.18) → hypothesis $\hat\mu(\emptyset)=1$; reason: the proofs of Lemmas 3.10 and 3.15 use $\hat\mu(\emptyset)=1$; read as part of the standing setup
--   - reading: Algorithm 3 ("lexicographically first", the while loop) → `alg3Step` with Mathlib's lexicographic order on lists; the loop run for $L=N+2\bar R(\lfloor\log_2|\mathcal F|\rfloor+1)$ iterations of a kernel that is the identity on terminal states; reason: by Lemma 3.9 the loop ends within $L$ iterations, so this is the paper's loop
--   - reading: Algorithm 2 (Line 11's "for some $y$"; "If $\xi=1$, add $w_{i,t}$ to $\mathcal T$; set $\mathcal G^{\mathrm{ret}}\leftarrow\dots$") → `alg2`: the least violating $y$ in the order of $\Sigma$; both actions under $\xi=1$; coins clamped to $[0,1]$; a trial with undefined $\bar\eta(\cdot\mid v)$ ends with nothing added; reason: the printed line leaves $y$ unspecified; clamping and the fallback act only on unreachable states
-- source:
--   Golowich, Moitra, Rohatgi, The Power of Test-Time Training for Approximate Sampling, arXiv:2606.11437 (version of November 3, 2026), Lemma 3.14, p.29 (PDF p.31)

import Mathlib
import Definitions.Def_TTTSampling_Assumption31
import Definitions.Def_TTTSampling_tvDist
import Definitions.Def_TTTSampling_alg3

namespace TTTSampling

/-- **Lemma 3.14.** For any `δ ∈ (0, 1/2)`, Algorithm 3 with the parameter `δ` outputs a sample
from a distribution `µ^alg` satisfying `D_TV(µ⋆, µ^alg) ≤ δ`.

Golowich, Moitra, Rohatgi, arXiv:2606.11437 (version of November 3, 2026), Lemma 3.14, printed
p.29 (PDF p.31).

**Formalization Note**
* "For an appropriate constant `C_N`" (Algorithm 3, Line 1): there is an absolute `C₀` such that
  the lemma holds for every `C_N ≥ C₀`.
* `x₀` is Line 14's "arbitrary fixed element of Σⁿ"; the lemma holds for each choice.
* Standing data as in Lemma 3.9, with `δ ∈ (0, 1/2)` as printed. -/
theorem lemma_3_14 :
    ∃ C₀ : ℕ, ∀ C_N : ℕ, C₀ ≤ C_N →
      ∀ {α : Type} [Fintype α] [LinearOrder α] {n : ℕ} (F : Finset (PMF (Fin n → α)))
        (R δ : ℝ) (μh : List α → NNReal) (μs : PMF (Fin n → α)) (x₀ : Fin n → α),
        1 ≤ n → 2 ≤ F.card → μs ∈ F → Assumption31 μs μh R → μh [] = 1 → 1 ≤ R →
        0 < δ → δ < 1 / 2 →
        tvDist μs ((alg3 C_N R δ F μh x₀).map Prod.fst) ≤ δ := by sorry

end TTTSampling
