-- Prove2me | Theorems.Thm_QPACLarge_eq_10
-- name    : QPACLarge.eq_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:05:24.616115+00:00
-- url     : https://prove2.me/theorems/c77a943c-4c3b-4ebd-b1ef-34d965b4de49
-- title:
--   Eq. (10) — $s(n)=\omega(\log n)$ and $n/2-s(n)=\omega(\log n)$
-- statement:
--   Let $\lambda_n > 0$, and let $s : \mathbb N \to \mathbb N$ satisfy $2^{-s(n)} \le \lambda_n \le 4 \cdot 2^{-s(n)}$ for all large $n$ (Eq. (9)). Assume $\lambda_n 2^{n/2} = n^{\omega(1)}$ and $\lambda_n = n^{-\omega(1)}$. Then
--
--   $$
--   s(n) = \omega(\log n), \qquad \frac n2 - s(n) = \omega(\log n). \tag{10}
--   $$
--
--   So the exponent $s(n)$ of the approximation $2^{-s(n)}$ of $\lambda_n$ grows faster than any multiple of $\log n$ and stays below $n/2$ by more than any multiple of $\log n$; this is what makes the padding length $m_n$ of Section 5.2 fit strictly between $\omega(\log n)$ and $n - \omega(\log n)$.
--
--   Differences from the source:
--   - reading: $\lambda_n 2^{n/2} = n^{\omega(1)}$, $\lambda_n = n^{-\omega(1)}$, $g = \omega(\log n)$ → for every $c \in \mathbb N$, eventually $n^c 2^{-n/2} \le \lambda_n$, $\lambda_n \le n^{-c}$, $c\log n \le g(n)$; reason: the standard meaning of $\omega(\cdot)$
--   - generalization: $s(n)$ output by the polynomial-time algorithm of Eq. (9) → any $s : \mathbb N \to \mathbb N$ with Eq. (9) eventually; reason: the derivation uses only Eq. (9); every constructive $s$ is such an $s$
-- source:
--   Oliveira, Unconditional Quantum PAC Learning Advantage in the Large Error Regime, arXiv:2610.23268 (held file sha256 e749e7c9…), Section 5, p.34, Eq. (10)

import Mathlib

namespace QPACLarge

open Filter

/-- **Eq. (10): `s(n) = ω(log n)` and `n/2 − s(n) = ω(log n)`.**
Oliveira, *Unconditional Quantum PAC Learning Advantage in the Large Error Regime*, arXiv:2610.23268 (held file sha256 e749e7c9…), Section 5, p.34: "Note that, under Equation (9), the assumptions `λₙ2^{n/2} = n^{ω(1)}` and
`λₙ = n^{−ω(1)}` yield `s(n) = ω(log n)`, `n/2 − s(n) = ω(log n)`. (10)"

**Formalization Note.** `g = ω(log n)` is read as: for every `c`, eventually `c log n ≤ g(n)`;
`λₙ2^{n/2} = n^{ω(1)}` as: for every `c`, eventually `n^c 2^{−n/2} ≤ λₙ`; `λₙ = n^{−ω(1)}` as: for
every `c`, eventually `λₙ ≤ n^{−c}`. Eq. (9) is assumed for an arbitrary `s` (no time bound). -/
theorem eq_10 (lam : ℕ → ℝ) (s : ℕ → ℕ) (hpos : ∀ n, 0 < lam n)
    (h9 : ∀ᶠ n : ℕ in atTop, ((2 : ℝ) ^ s n)⁻¹ ≤ lam n ∧ lam n ≤ 4 * ((2 : ℝ) ^ s n)⁻¹)
    (hlow : ∀ c : ℕ, ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ c * (2 : ℝ) ^ (-(n : ℝ) / 2) ≤ lam n)
    (hup : ∀ c : ℕ, ∀ᶠ n : ℕ in atTop, lam n ≤ (n : ℝ) ^ (-(c : ℝ))) :
    (∀ c : ℕ, ∀ᶠ n : ℕ in atTop, (c : ℝ) * Real.log n ≤ s n) ∧
      (∀ c : ℕ, ∀ᶠ n : ℕ in atTop, (c : ℝ) * Real.log n ≤ (n : ℝ) / 2 - s n) := by sorry

end QPACLarge
