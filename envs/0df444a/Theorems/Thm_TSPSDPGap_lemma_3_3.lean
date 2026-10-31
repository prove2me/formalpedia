-- Prove2me | Theorems.Thm_TSPSDPGap_lemma_3_3
-- name    : TSPSDPGap.lemma_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:37:28.50373+00:00
-- url     : https://prove2.me/theorems/60850c3a-3b37-47d0-9d02-ba488f20b318
-- title:
--   Lemma 3.3 (Gray) — eigenvalues and eigenvectors of a circulant matrix
-- statement:
--   Let $n\in\mathbb N$, $m_0,\dots,m_{n-1}\in\mathbb C$, and let $M$ be the circulant matrix with entry $m_{(t-s)\bmod n}$ in row $s$ and column $t$. For $t=0,\dots,n-1$ put $w_t=e^{-2\pi t\sqrt{-1}/n}$, $v_t=(1,w_t,w_t^2,\dots,w_t^{n-1})$ and
--   $$
--   \lambda_t=\sum_{s=0}^{n-1}m_s\,w_t^{\,s}.
--   $$
--   Then $Mv_t=\lambda_tv_t$ and $v_t\neq0$ for every $t$, and the eigenvalues of $M$ are exactly $\lambda_0,\dots,\lambda_{n-1}$.
--
--   The lemma gives the spectrum of every circulant matrix; the paper uses it for the circulant blocks $A$ and $B$ of its feasible solutions.
--
--   **Formalization Note** The spectrum is `spectrum ℂ M`. The printed case $t=n$, with $\lambda_n=\sum_s m_s$, is the index $t=0$ here ($w_0=1$).
--
--   Differences from the source:
--   - generalization: a circulant matrix with (real) entries m_s → m : Fin n → ℂ; reason: the lemma holds for complex entries; real circulants are the special case the paper uses
--   - reading: eigenvalue index t = 1, …, n − 1 and t = n (λ_n = Σ m_s); eigenvector index t = 0, …, n − 1 → one index t ∈ Fin n, with t = 0 for the printed t = n; reason: the printed λ_n and v_0 are the same eigenpair (w_n = w_0 = 1); the lemma mixes the two index ranges
--   - encoding: 1-based indices → 0-based Fin n indices; reason: Lean convention; same instances
-- source:
--   Gutekunst & Williamson, SDP Relaxations of the TSP and Their Integrality Gaps, arXiv:1907.09054v1, Lemma 3.3, p.9

import Mathlib

namespace TSPSDPGap

/-- **Lemma 3.3 (Gray [12]): eigenvalues and eigenvectors of a circulant matrix.**
Gutekunst & Williamson, *SDP Relaxations of the TSP and Their Integrality Gaps*,
arXiv:1907.09054v1, Lemma 3.3, p.9:
"The circulant matrix M = (m_{(t−s) mod n})_{s,t=1}^n has eigenvalues
λ_t(M) = Σ_{s=0}^{n−1} m_s e^{−2πst√−1/n} if t = 1, ..., n − 1, and Σ_{s=0}^{n−1} m_s if t = n.
The eigenvector corresponding to eigenvalue λ_t is v_t = (1, w_t, w_t², ..., w_t^{n−1}) for
t = 0, 1, ..., n − 1 with w_t = e^{−2πt√−1/n}."

For every `n` and every `m : Fin n → ℂ`, the matrix `M` with entry `m_{(t − s) mod n}` in row
`s`, column `t` satisfies `M v_t = λ_t v_t` with `v_t ≠ 0` for every `t`, and the spectrum of
`M` is exactly `{λ_t}`.

**Formalization Note.** Indices are `Fin n` (0-based), `t − s` is subtraction in `Fin n`
(mod `n`). The printed case `t = n` is `t = 0` here (`w_0 = 1`, `λ_0 = Σ m_s`). The entries are
complex (the paper applies the lemma to real symmetric circulants). -/
theorem lemma_3_3 (n : ℕ) (m : Fin n → ℂ) :
    let M : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun s t => m (t - s)
    let w : Fin n → ℂ := fun t =>
      Complex.exp (-2 * (Real.pi : ℂ) * ((t : ℕ) : ℂ) * Complex.I / (n : ℂ))
    let v : Fin n → Fin n → ℂ := fun t u => w t ^ (u : ℕ)
    let lam : Fin n → ℂ := fun t => ∑ s : Fin n, m s * w t ^ (s : ℕ)
    (∀ t : Fin n, M.mulVec (v t) = lam t • v t ∧ v t ≠ 0) ∧ spectrum ℂ M = Set.range lam := by sorry

end TSPSDPGap
