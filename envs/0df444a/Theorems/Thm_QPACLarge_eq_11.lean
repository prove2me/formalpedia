-- Prove2me | Theorems.Thm_QPACLarge_eq_11
-- name    : QPACLarge.eq_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:06:38.398761+00:00
-- url     : https://prove2.me/theorems/b8d0f809-46de-42aa-89c6-fe0c62a2b3fb
-- title:
--   Eq. (11) — $M_n\theta_n^2=16r_n^3$, $M_n\lambda_n^2\le256r_n^3$, $M_n\theta_n/r_n=16r_n^2/\theta_n=n^{\omega(1)}$, and $1\le m_n<n$
-- statement:
--   Let $\lambda_n > 0$, and let $s : \mathbb N \to \mathbb N$ satisfy $2^{-s(n)} \le \lambda_n \le 4 \cdot 2^{-s(n)}$ for all large $n$ (Eq. (9)). Assume $\lambda_n 2^{n/2} = n^{\omega(1)}$ and $\lambda_n = n^{-\omega(1)}$. Fix an integer $k \ge 1$ and set $r_n = 2^{k\lceil\log_2 n\rceil}$, $\theta_n = 2^{-s(n)}$, $m_n = 2s(n) + 3k\lceil\log_2 n\rceil + 4$ and $M_n = 2^{m_n}$. Then $m_n = \omega(\log n)$, $n - m_n = \omega(\log n)$, $1 \le m_n < n$ for all large $n$, and
--
--   $$
--   M_n\theta_n^2 = 16 r_n^3, \qquad M_n\lambda_n^2 \le 256 r_n^3, \qquad \frac{M_n\theta_n}{r_n} = \frac{16 r_n^2}{\theta_n} = n^{\omega(1)}. \tag{11}
--   $$
--
--   The first and third identities hold for every $n$; the second inequality holds for all large $n$. These parameter estimates feed both the quantum upper bound and the classical lower bound in the proof of Theorem 1.5.
--
--   Differences from the source:
--   - reading: $\lambda_n 2^{n/2} = n^{\omega(1)}$, $\lambda_n = n^{-\omega(1)}$, $g = \omega(\log n)$ → for every $c \in \mathbb N$, eventually $n^c 2^{-n/2} \le \lambda_n$, $\lambda_n \le n^{-c}$, $c\log n \le g(n)$; reason: the standard meaning of $\omega(\cdot)$
--   - generalization: $s(n)$ output by the polynomial-time algorithm of Eq. (9) → any $s : \mathbb N \to \mathbb N$ with Eq. (9) eventually; reason: the derivation uses only Eq. (9); every constructive $s$ is such an $s$
--   - encoding: $\lceil\log_2 n\rceil$ → `Nat.clog 2 n`; reason: equal for every $n \ge 1$
-- source:
--   Oliveira, Unconditional Quantum PAC Learning Advantage in the Large Error Regime, arXiv:2610.23268 (held file sha256 e749e7c9…), Section 5.2, p.36, Eq. (11) and the sentence before it

import Mathlib
import Definitions.Def_QPACLarge_rN
import Definitions.Def_QPACLarge_mN

namespace QPACLarge

open Filter

/-- **Eq. (11) and `1 ≤ mₙ < n`.**
Oliveira, *Unconditional Quantum PAC Learning Advantage in the Large Error Regime*, arXiv:2610.23268 (held file sha256 e749e7c9…), Section 5.2, p.36: with `θₙ ≜ 2^{−s(n)}`, `mₙ ≜ 2s(n) + 3k⌈log₂ n⌉ + 4`,
`Mₙ ≜ 2^{mₙ} = 16rₙ³/θₙ²`: "The two asymptotic conditions in Equation (10) give `mₙ = ω(log n)` and
`n − mₙ = ω(log n)`. Thus `1 ≤ mₙ < n` eventually. The parameter choice has three useful
consequences: `Mₙθₙ² = 16rₙ³`, `Mₙλₙ² ≤ 256rₙ³`, `Mₙθₙ/rₙ = 16rₙ²/θₙ = n^{ω(1)}`. (11)"

**Formalization Note.** `k` is a positive integer ("Assume without loss of generality that `k` is an
integer", p.33); `rₙ = 2^{k⌈log₂ n⌉}` (`rN`). Eq. (9) for `s` and the two growth conditions on `λ`
are the hypotheses of Eq. (10). `ω(·)` is read as in `eq_10`. -/
theorem eq_11 (k : ℕ) (hk : 1 ≤ k) (lam : ℕ → ℝ) (s : ℕ → ℕ) (hpos : ∀ n, 0 < lam n)
    (h9 : ∀ᶠ n : ℕ in atTop, ((2 : ℝ) ^ s n)⁻¹ ≤ lam n ∧ lam n ≤ 4 * ((2 : ℝ) ^ s n)⁻¹)
    (hlow : ∀ c : ℕ, ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ c * (2 : ℝ) ^ (-(n : ℝ) / 2) ≤ lam n)
    (hup : ∀ c : ℕ, ∀ᶠ n : ℕ in atTop, lam n ≤ (n : ℝ) ^ (-(c : ℝ))) :
    (∀ c : ℕ, ∀ᶠ n : ℕ in atTop, (c : ℝ) * Real.log n ≤ mN k n (s n)) ∧
    (∀ c : ℕ, ∀ᶠ n : ℕ in atTop, (c : ℝ) * Real.log n ≤ (n : ℝ) - mN k n (s n)) ∧
    (∀ᶠ n : ℕ in atTop, 1 ≤ mN k n (s n) ∧ mN k n (s n) < n) ∧
    (∀ n : ℕ, (2 : ℝ) ^ mN k n (s n) * (((2 : ℝ) ^ s n)⁻¹) ^ 2 = 16 * (rN k n : ℝ) ^ 3) ∧
    (∀ᶠ n : ℕ in atTop, (2 : ℝ) ^ mN k n (s n) * lam n ^ 2 ≤ 256 * (rN k n : ℝ) ^ 3) ∧
    (∀ n : ℕ, (2 : ℝ) ^ mN k n (s n) * ((2 : ℝ) ^ s n)⁻¹ / rN k n =
      16 * (rN k n : ℝ) ^ 2 / ((2 : ℝ) ^ s n)⁻¹) ∧
    (∀ c : ℕ, ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ c ≤ 16 * (rN k n : ℝ) ^ 2 / ((2 : ℝ) ^ s n)⁻¹) := by sorry

end QPACLarge
