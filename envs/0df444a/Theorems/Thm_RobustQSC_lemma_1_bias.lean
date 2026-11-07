-- Prove2me | Theorems.Thm_RobustQSC_lemma_1_bias
-- name    : RobustQSC.lemma_1_bias
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:48:44.335169+00:00
-- url     : https://prove2.me/theorems/305db2d1-4d2e-4352-a379-e217278f29df
-- title:
--   Lemma 1, p.19 — bias of Porter–Thomas measures
-- statement:
--   Let $\mu$ be $\mathrm{Dirichlet}(\vec1)$ on $N=2^n$ coordinates, and let
--
--   $$
--   \mathrm{Bias}(\mu)=\max_{s\ne0^n}\sqrt N|\hat\mu(s)|=\max_{s\ne0^n}\Bigl|\sum_x\mu(x)(-1)^{s\cdot x}\Bigr|.
--   $$
--
--   Then with probability at least $1-2^{-\Omega(n)}$,
--
--   $$
--   \mathrm{Bias}(\mu)\le O\bigl(\sqrt{n/N}\bigr).
--   $$
--
--   A typical measure thus has small Fourier bias, which makes the Fourier coefficients of a random phase state with that measure nearly uncorrelated.
--
--   Differences from the source:
--   - reading: the second form of the display for $\mathrm{Bias}(\mu)$ has no absolute value → the absolute value throughout; reason: the first form and the proof bound the absolute value; this form implies the other
--   - encoding: $\max_{s\ne0}$ of the sum → a bound for every $s\ne0$; reason: equivalent; avoids a maximum over an empty set at $n=0$
--   - encoding: "with probability $1-2^{-\Omega(n)}$", "for $n$ large" → a constant $c_0>0$ and a threshold $n_0$ with the outer measure of the failure event at most $2^{-c_0n}$ for $n\ge n_0$; reason: the standard meaning; the failure event is bounded in outer measure, so no measurability is assumed
-- source:
--   Coladangelo, Li, Slote, Robust quantum state certification and uncertainty principles for total influence, arXiv:2607.27184 (sha256 09d2692e…), Lemma 1, p.19; Bias, §3.2, p.19

import Definitions.Def_RobustQSC_dirichletOne
import Definitions.Def_QAlgorithms_Defs_Basic

namespace RobustQSC

open QAlgorithms MeasureTheory

/-- **Lemma 1 (Bias of Porter–Thomas measures).** Let `μ` be `Dirichlet(1⃗)` on `N = 2ⁿ`
coordinates. Then with probability at least `1 − 2^{−Ω(n)}`,
`Bias(μ) = max_{s ≠ 0} |Σ_x μ(x)(−1)^{s·x}| ≤ O(√(n/N))`.

Source: Coladangelo, Li, Slote, *Robust quantum state certification and uncertainty principles for
total influence*, arXiv:2607.27184 (sha256 09d2692e…), Lemma 1, p.19; `Bias(μ) = max_{s≠0ⁿ} √N |μ̂(s)|`, §3.2, p.19.

**Formalization Note.** `O(·)` and `Ω(·)` are pinned as constants `C` and `c₀ > 0` chosen before
`n`, for `n ≥ n₀`. The bias is `max_{s≠0} √N|μ̂(s)| = max_{s≠0} |Σ_x μ(x)(−1)^{s·x}|` (the
p.19 display drops the absolute value in its second form; the proof bounds the absolute
value). The maximum is written as a bound for every `s ≠ 0`. -/
theorem lemma_1_bias :
    ∃ C c₀ : ℝ, 0 < c₀ ∧ ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      dirichletOne (Qubits n) {μ | ¬ ∀ s : Qubits n, s ≠ (fun _ => false) →
          |∑ x, μ x * (if dotBits s x then -1 else 1)| ≤ C * Real.sqrt (n / 2 ^ n)}
        ≤ ENNReal.ofReal ((2 : ℝ) ^ (-(c₀ * n))) := by sorry

end RobustQSC
