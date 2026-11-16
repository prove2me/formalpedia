-- Prove2me | Theorems.Thm_QMomentMatch_FirstBound_Supplement_lemma_3_3
-- name    : QMomentMatch.FirstBound.Supplement.lemma_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:41:25.287204+00:00
-- url     : https://prove2.me/theorems/6d89c108-ae82-4d19-81d6-0864e9085a38
-- title:
--   Lemma 3.3 — Newton bound: $|q(z)-Q_r(z)|\le\frac{2}{(2r)!}\left(\frac{4d^2}{H}\right)^r z^r$ at integers $z\in\{0,\dots,H\}$
-- statement:
--   Let $H\ge1$ and $d\ge0$ be integers, and let $q$ be a real polynomial of degree at most $d$ with $|q(z)|\le1$ for every $z\in\{0\}\cup[H]=\{0,1,\dots,H\}$. Its **Newton coefficients** are
--   $$d_\ell=\sum_{s=0}^{\ell}(-1)^{\ell-s}\binom{\ell}{s}q(s)\qquad(0\le\ell\le H),$$
--   and for an integer $1\le r\le H+1$ put $Q_r(z)=\sum_{\ell=0}^{r-1}d_\ell\binom z\ell$.
--
--   1. At every $z\in\{0\}\cup[H]$,
--   $$q(z)-Q_r(z)=\sum_{\ell=r}^{H}d_\ell\binom z\ell=\sum_{\ell=r}^{z}d_\ell\binom z\ell,$$
--   empty sums being zero.
--   2. If moreover $d^2\le H/2$, then for every integer $1\le r\le H+1$ and every $z\in\{0\}\cup[H]$,
--   $$|q(z)-Q_r(z)|\le\frac{2}{(2r)!}\left(\frac{4d^2}{H}\right)^r z^r.\qquad(11)$$
--
--   This is the Newton-basis counterpart of the Taylor bound (Lemma 3.2). In the proof of Theorem 2.6 it controls the part of $q_{\mathbf w}$ beyond its first $r$ Newton terms, and applied at $z=\ell$ with remainder order $\ell$ it bounds the single coefficient $d_\ell$ in the singleton case (Lemma 4.8).
--
--   **Formalization Note** $\binom z\ell$ is the natural-number binomial coefficient at integer $z$; both parts are stated only at integer points, as in the source.
--
--   Differences from the source:
--   - encoding: Q_r(z) = Σ_{ℓ=0}^{r−1} d_ℓ (z choose ℓ) as a polynomial → the sum evaluated at natural numbers z ≤ H with Nat.choose; reason: the lemma only asserts statements at z ∈ {0} ∪ [H]
--   - encoding: q(z) for a polynomial q of degree at most d → q : ℝ[X] with q.natDegree ≤ d, evaluated with Polynomial.eval; reason: natDegree ≤ d is degree ≤ d (the zero polynomial included)
-- source:
--   Chandrima Kayal, Frédéric Magniez, Sayantan Sen, Dániel Szabó, STOC 2027 submission #564 (October 2026), Lemma 3.3, p. 16 (proof: Appendix A, p. 43)

import Mathlib
import Definitions.Def_QMomentMatch_FirstBound_Supplement_NewtonCoeff

namespace QMomentMatch.FirstBound.Supplement

open Polynomial

/-- Lemma 3.3 (Newton bound), p. 16 (proof: Appendix A, p. 43). `d_ℓ` are the Newton
coefficients of `q` and `Q_r(z) = ∑_{ℓ=0}^{r−1} d_ℓ (z choose ℓ)`; both parts are stated at the
integers `z ∈ {0} ∪ [H]`. -/
theorem lemma_3_3 (H d : ℕ) (hH : 1 ≤ H) (q : ℝ[X]) (hq : q.natDegree ≤ d)
    (hbound : ∀ z : ℕ, z ≤ H → |q.eval (z : ℝ)| ≤ 1) :
    (∀ r : ℕ, 1 ≤ r → r ≤ H + 1 → ∀ z : ℕ, z ≤ H →
      q.eval (z : ℝ) - ∑ ℓ ∈ Finset.range r,
          newtonCoeff (fun s => q.eval (s : ℝ)) ℓ * ((z.choose ℓ : ℕ) : ℝ) =
        ∑ ℓ ∈ Finset.Ico r (H + 1),
          newtonCoeff (fun s => q.eval (s : ℝ)) ℓ * ((z.choose ℓ : ℕ) : ℝ) ∧
      ∑ ℓ ∈ Finset.Ico r (H + 1),
          newtonCoeff (fun s => q.eval (s : ℝ)) ℓ * ((z.choose ℓ : ℕ) : ℝ) =
        ∑ ℓ ∈ Finset.Ico r (z + 1),
          newtonCoeff (fun s => q.eval (s : ℝ)) ℓ * ((z.choose ℓ : ℕ) : ℝ)) ∧
    ((d : ℝ) ^ 2 ≤ (H : ℝ) / 2 → ∀ r : ℕ, 1 ≤ r → r ≤ H + 1 → ∀ z : ℕ, z ≤ H →
      |q.eval (z : ℝ) - ∑ ℓ ∈ Finset.range r,
          newtonCoeff (fun s => q.eval (s : ℝ)) ℓ * ((z.choose ℓ : ℕ) : ℝ)| ≤
        2 / ((2 * r).factorial : ℝ) * (4 * (d : ℝ) ^ 2 / H) ^ r * (z : ℝ) ^ r) := by sorry

end QMomentMatch.FirstBound.Supplement
