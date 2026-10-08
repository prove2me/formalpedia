-- Prove2me | Theorems.Thm_QueueingFundamentals_Numerical_phi_recursion
-- name    : QueueingFundamentals.Numerical.phi_recursion
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T20:24:44.887282+00:00
-- url     : https://prove2.me/theorems/33de33f0-5950-40fe-b765-593ff116f789
-- title:
--   Eqs. (8.13)–(8.14) — the recursion $\phi^{(k)} = \phi^{(k-1)}\tilde P$
-- statement:
--   Let $Q$ be a generator on $\{0,1,\dots,N\}$ with exit rates $q_i=\sum_{j\ne i}q_{ij}$, let $\Lambda>0$ with $\Lambda\ge q_i$ for all $i$, let $\tilde P=Q/\Lambda+I$, and let $p(0)$ be a probability vector. Put $\phi^{(k)}=p(0)\tilde P^{(k)}$ for $k\ge 0$. Then
--
--   $$\phi^{(k)}=\phi^{(k-1)}\tilde P\qquad (k\ge 1),$$
--
--   and every $\phi^{(k)}$ is a probability vector: it is the state distribution of the uniformized chain $Y_k$ after $k$ occurrences of the Poisson($\Lambda$) process.
--
--   With this recursion the truncated sum (8.11) is computed as $\sum_{k=0}^{T(t,\epsilon)}\phi^{(k)}e^{-\Lambda t}(\Lambda t)^k/k!$ (8.14) without forming matrix powers.
-- source:
--   Gross, Shortle, Thompson & Harris, Fundamentals of Queueing Theory, 4th ed., Wiley 2008, DOI 10.1002/9781118625651, p.384, Eqs. (8.13)–(8.14)

import Mathlib
import Definitions.Def_QueueingFundamentals_Numerical_Uniformization

open Matrix

namespace QueueingFundamentals.Numerical

/-- Eqs. (8.13)–(8.14) (Gross et al., p.384): for a generator `Q`, `Λ > 0` with `Λ ≥ q_i` for
all `i`, and an initial probability vector `p(0)`, the vectors `φ^{(k)} = p(0) P̃^{(k)}` satisfy the
recursion `φ^{(k)} = φ^{(k−1)} P̃` and each `φ^{(k)}` is a probability vector (the distribution of
the uniformized chain `Y_k` after `k` transitions). -/
theorem phi_recursion {N : ℕ} (Q : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (hQ : IsGenerator Q) (Λ : ℝ) (hΛ : 0 < Λ) (hΛq : ∀ i, exitRate Q i ≤ Λ)
    (p₀ : Fin (N + 1) → ℝ) (hp₀ : IsProbVec p₀) :
    (∀ k : ℕ, 1 ≤ k → phi Λ Q p₀ k = phi Λ Q p₀ (k - 1) ᵥ* uniformizedMatrix Λ Q) ∧
      ∀ k : ℕ, IsProbVec (phi Λ Q p₀ k) := by sorry

end QueueingFundamentals.Numerical
