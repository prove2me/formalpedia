-- Prove2me | Theorems.Thm_PercolationGames_subadditive_error_tendsto
-- name    : PercolationGames.subadditive_error_tendsto
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:24:34.32606+00:00
-- url     : https://prove2.me/theorems/e1f755f2-52b2-48dd-8edc-48627024ab60
-- title:
--   [13] (de Bruijn–Erdős), p.6 — a subadditive sequence with error term $f$, $\sum f(n)/n^2<\infty$, has $a_n/n$ convergent in $[-\infty,\infty)$
-- statement:
--   Let $(a_n)_{n\ge1}$ and $(f(n))_{n\ge1}$ be real sequences with $f$ non-negative and non-decreasing,
--
--   $$\sum_{n\ge1}\frac{f(n)}{n^2}<+\infty,\qquad a_{m+n}\le a_m+a_n+f(m+n)\quad\text{for all }m,n\ge1.$$
--
--   Then $a_n/n$ converges in $[-\infty,\infty)$: either $a_n/n\to-\infty$, or $a_n/n\to\ell$ for some $\ell\in\mathbb R$.
--
--   This is de Bruijn and Erdős's extension of Fekete's lemma to subadditive sequences with an error term. The paper applies it to $a_n=-n\mathbb E(v_n)$ and $f(n)=D\ln(n+1)^{1/2}n^{1/2}$; there $a_n/n=-\mathbb E(v_n)$ is bounded, so the limit is finite and $\mathbb E(v_n)$ converges.
--
--   **Formalization Note** The hypotheses only involve indices $n\ge1$; the values $a_0$, $f(0)$ play no role. The series condition is summability of $n\mapsto f(n+1)/(n+1)^2$.
--
--   Differences from the source:
--   - generalization: a_n := −nE(v_n), f(n) := D ln(n+1)^{1/2} n^{1/2} → any real sequences a, f with the stated properties; reason: this is the lemma of [13] that the paper invokes; the paper's a and f are an instance
--   - reading: By [13], a_n/n converges → a_n/n → −∞ or a_n/n has a real limit; reason: [13] gives a limit in [−∞, ∞); for a general sequence the limit −∞ occurs (a_n = −n², f = 0), while for the paper's bounded a_n/n = −E(v_n) the real alternative holds
--   - encoding: Σ_{n≥1} f(n)/n² < +∞ → Summable (fun n => f (n+1) / (n+1)²); reason: the terms are non-negative, so summability is convergence of the series
-- source:
--   Garnier–Ziliotto, Percolation games, arXiv:2110.12227v2, §3.1, p.6, citing [13] N. G. de Bruijn and P. Erdős, Some linear and some quadratic recursion formulas II, Proc. Koninklijke Nederlandse Akademie van Wetenschappen Ser. A 14 (1952), 152–163

import Mathlib
import Definitions.Def_PercolationGames_Model

open MeasureTheory ProbabilityTheory Filter Topology

namespace PercolationGames

/-- De Bruijn–Erdős: subadditive sequences with an error term. Let `f` be non-negative and
non-decreasing on `n ≥ 1` with `∑_{n ≥ 1} f(n)/n² < ∞`, and let `a_{m+n} ≤ a_m + a_n + f(m + n)`
for all `m, n ≥ 1`. Then `a_n / n` converges in `[−∞, ∞)`: either `a_n / n → −∞` or `a_n / n`
has a real limit.

Source: Garnier–Ziliotto, *Percolation games*, arXiv:2110.12227v2, §3.1, p.6, citing [13] (N. G. de Bruijn, P. Erdős, *Some linear and some
quadratic recursion formulas II*, Proc. Koninklijke Nederlandse Akademie van Wetenschappen Ser. A 14 (1952), 152–163).

**Formalization Note.** Only the values at `n ≥ 1` enter the hypotheses; `a 0`, `f 0` are
irrelevant. The paper's "a_n/n converges" is for its bounded sequence `a_n = −n 𝔼(v_n)`; for
a general sequence the limit may be `−∞` (e.g. `a_n = −n²`, `f = 0`). -/
theorem subadditive_error_tendsto (a f : ℕ → ℝ)
    (hf_nonneg : ∀ n, 1 ≤ n → 0 ≤ f n)
    (hf_mono : ∀ m n, 1 ≤ m → m ≤ n → f m ≤ f n)
    (hf_sum : Summable fun n : ℕ => f (n + 1) / ((n : ℝ) + 1) ^ 2)
    (ha : ∀ m n, 1 ≤ m → 1 ≤ n → a (m + n) ≤ a m + a n + f (m + n)) :
    Tendsto (fun n : ℕ => a n / n) atTop atBot ∨
      ∃ ℓ : ℝ, Tendsto (fun n : ℕ => a n / n) atTop (𝓝 ℓ) := by sorry

end PercolationGames
