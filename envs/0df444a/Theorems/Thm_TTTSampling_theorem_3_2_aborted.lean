-- Prove2me | Theorems.Thm_TTTSampling_theorem_3_2_aborted
-- name    : TTTSampling.theorem_3_2_aborted
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:44:23.510045+00:00
-- url     : https://prove2.me/theorems/1d49d469-f9bb-4f11-9906-1dc0c5389fc1
-- title:
--   Proof of Theorem 3.2 (corrected: threshold's $\delta$-factors at $\min(\delta,1/2)$) — Algorithm 3 with the abort rule
-- statement:
--   There is an absolute constant $C_0$ such that for every $C_{\mathsf N}\ge C_0$ there is $C>0$ with the following property. Let $n\ge1$, $|\mathcal F|\ge2$, $\mu^\star\in\mathcal F$, $\hat\mu$ satisfying Assumption 3.1 with parameter $R\ge1$ and $\hat\mu(\emptyset)=1$, $\delta\in(0,1)$ and $x_0\in\Sigma^n$. Run Algorithm 3 with tolerance $\delta/2$, aborting with output $x_0$ as soon as the number of oracle calls would exceed
--
--   $$
--   \theta=C\, n\,|\Sigma|\,R^{12}\sqrt{\log|\mathcal F|}\,\log\frac1{\delta'}\,\log\frac{R\log|\mathcal F|}{\delta'},\qquad\delta'=\min(\delta,1/2).
--   $$
--
--   Then the output distribution $\hat\nu$ satisfies $D_{\mathrm{TV}}(\mu^\star,\hat\nu)\le\delta$, and every run makes at most $\theta$ oracle calls.
--
--   This is the concrete algorithm behind Theorem 3.2; the theorem follows from it together with trivial exact samplers for $|\mathcal F|=1$ and $n=0$.
--
--   **Formalization Note** The count clause holds by construction of the abort; the content is the total-variation clause (Lemmas 3.14 and 3.15 at $\delta/2$).
--
--   Differences from the source:
--   - correction: the threshold (34) $O(n|\Sigma|R^{12}\sqrt{\log|\mathcal F|}\log\frac1\delta\log\frac{R\log|\mathcal F|}\delta)$ for $\delta\in(0,1)$ → the same expression with both $\delta$-factors at $\delta'=\min(\delta,1/2)$; reason: as printed the threshold tends to $0$ as $\delta\to1$, so for $\delta$ near $1$ every run with $\ge1$ call aborts and the output is the fixed $x_0$, which is not within $\delta$ of $\mu^\star$ when $\mu^\star$ is spread (e.g. uniform on $\{0,1\}^n$, $\delta=1-2^{1-n}$); for $\delta\le1/2$ the threshold is the printed one
--   - reading: "for an appropriate constant $C_{\mathsf N}$" and the $O(\cdot)$ of (34) → $\exists C_0\,\forall C_{\mathsf N}\ge C_0\,\exists C>0$; reason: the threshold must grow with $C_{\mathsf N}$ (the count is proportional to $N$)
--   - encoding: "whenever its number of oracle calls reaches the threshold in (34), it aborts and outputs an arbitrary symbol" → runs whose count exceeds $\theta$ are replaced by $(x_0,\lfloor\theta\rfloor)$ in the joint law of (output, count), for every $x_0$; reason: an aborted run stops at the threshold; the replacement string is arbitrary
--   - encoding: $n$ a positive integer, $\mathcal F$ finite (Algorithm 3's input) → $1\le n$ and $2\le|\mathcal F|$; reason: Line 4 queries strings of length $1$; at $|\mathcal F|=1$ the formula for $N$ contains $\log 0$; only excludes undefined cases
--   - reading: "We also adopt the convention that $\mu(\emptyset)=1$" (p.18) → hypothesis $\hat\mu(\emptyset)=1$; reason: the proofs of Lemmas 3.10 and 3.15 use $\hat\mu(\emptyset)=1$; read as part of the standing setup
--   - reading: Algorithm 3 ("lexicographically first", the while loop) → `alg3Step` with Mathlib's lexicographic order on lists; the loop run for $L=N+2\bar R(\lfloor\log_2|\mathcal F|\rfloor+1)$ iterations of a kernel that is the identity on terminal states; reason: by Lemma 3.9 the loop ends within $L$ iterations, so this is the paper's loop
--   - reading: Algorithm 2 (Line 11's "for some $y$"; "If $\xi=1$, add $w_{i,t}$ to $\mathcal T$; set $\mathcal G^{\mathrm{ret}}\leftarrow\dots$") → `alg2`: the least violating $y$ in the order of $\Sigma$; both actions under $\xi=1$; coins clamped to $[0,1]$; a trial with undefined $\bar\eta(\cdot\mid v)$ ends with nothing added; reason: the printed line leaves $y$ unspecified; clamping and the fallback act only on unreachable states
-- source:
--   Golowich, Moitra, Rohatgi, The Power of Test-Time Training for Approximate Sampling, arXiv:2606.11437 (version of November 3, 2026), proof of Theorem 3.2, p.32 (PDF p.34), (34)

import Mathlib
import Definitions.Def_TTTSampling_Assumption31
import Definitions.Def_TTTSampling_tvDist
import Definitions.Def_TTTSampling_alg3Abort

namespace TTTSampling

/-- **Proof of Theorem 3.2: Algorithm 3 with the abort rule** (corrected: the threshold's
δ-factors at `min(δ, 1/2)`). "We can modify Algorithm 3 so that, whenever its number of oracle
calls reaches the threshold in (34), it aborts and outputs an arbitrary symbol. This changes its
output distribution by at most δ/2 in total variation distance, meaning that the resulting output
distribution, which we denote by ν̂, satisfies D_TV(µ⋆, ν̂) ≤ δ."

Golowich, Moitra, Rohatgi, arXiv:2606.11437 (version of November 3, 2026), proof of Theorem 3.2,
printed p.32 (PDF p.34), with (34).

**Formalization Note**
* `alg3Abort C_N C R δ` runs Algorithm 3 with tolerance `δ/2` and aborts above the threshold
  `C · qBound n |Σ| R |ℱ| (min δ (1/2))`. There is an absolute `C₀` such that for every
  `C_N ≥ C₀` some `C > 0` (depending on `C_N` only) gives, for every instance: TV at most `δ`
  from `µ⋆`, and at most the threshold of oracle calls on every run.
* The count clause holds by construction of the abort; the content is the TV clause.
* **Correction** as in Theorem 3.2: the δ-factors at `min(δ, 1/2)` (the printed threshold
  tends to `0` as `δ → 1`).
* Standing data as in Lemma 3.9, with `δ ∈ (0, 1)`. -/
theorem theorem_3_2_aborted :
    ∃ C₀ : ℕ, ∀ C_N : ℕ, C₀ ≤ C_N → ∃ C : ℝ, 0 < C ∧
      ∀ {α : Type} [Fintype α] [LinearOrder α] {n : ℕ} (F : Finset (PMF (Fin n → α)))
        (R δ : ℝ) (μh : List α → NNReal) (μs : PMF (Fin n → α)) (x₀ : Fin n → α),
        1 ≤ n → 2 ≤ F.card → μs ∈ F → Assumption31 μs μh R → μh [] = 1 → 1 ≤ R →
        0 < δ → δ < 1 →
        tvDist μs ((alg3Abort C_N C R δ F μh x₀).map Prod.fst) ≤ δ ∧
        ∀ r ∈ (alg3Abort C_N C R δ F μh x₀).support,
          (r.2 : ℝ) ≤ C * qBound n (Fintype.card α) R F.card (min δ (1 / 2)) := by sorry

end TTTSampling
