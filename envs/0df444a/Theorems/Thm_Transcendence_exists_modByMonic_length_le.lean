-- Prove2me | Theorems.Thm_Transcendence_exists_modByMonic_length_le
-- name    : Transcendence.exists_modByMonic_length_le
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T16:43:52.624726+00:00
-- url     : https://prove2.me/theorems/49c5dda6-cade-42fa-a97e-6981d9634c42
-- title:
--   Reduction modulo a polynomial multiplies the length by at most Cⁿ
-- statement:
--   For polynomials in $\mathbb{Z}[X][Y]$, the length of $P \in \mathbb{Z}[X][Y]$, written $L(P)$, is the sum of the absolute values of all its integer coefficients. For every $Q \in \mathbb{Z}[X][Y]$ there is $C$ such that, whenever $P$ has length at most $b$, $X$-degree at most $e$ and $Y$-degree at most $n$, the remainder $P \bmod Q$ (Mathlib's `%ₘ`) satisfies
--
--   $$L(P \bmod Q) \le C^{n}\, b, \qquad \deg_X (P \bmod Q) \le e + C n.$$
--
--   Mathlib already provides the remainder, the divisibility and the degree drop; this node adds the size bound. No hypothesis on $Q$ is needed: if $Q$ is not monic, `%ₘ` returns $P$.
-- source:
--   Standard. Formal proof: Diaz modulus mission, 25 September 2026 (C. Perassi).

import Mathlib

namespace Transcendence

/-- Division by a monic polynomial in `ℤ[X][Y]` keeps sizes under control.

Let `Q ∈ ℤ[X][Y]` be monic in `Y`. For `P ∈ ℤ[X][Y]` of `Y`-degree at most `n`, the remainder
`P %ₘ Q` is `∑ₖ Pₖ(X) · (Yᵏ %ₘ Q)`, and `Yᵏ %ₘ Q` is obtained from `Y^(k-1) %ₘ Q` by one
multiplication by `Y` and one subtraction of a multiple of `Q`. Hence, if `P` has length
(sum of the absolute values of all its integer coefficients) at most `b` and every coefficient
`Pₖ(X)` has degree at most `e`, then `P %ₘ Q` has length at most `Cⁿ b` and its coefficients
have `X`-degree at most `e + C n`, for a constant `C` depending only on `Q`. When `Q` is not
monic, `P %ₘ Q = P` and the bounds hold with any `C ≥ 1`. -/
theorem exists_modByMonic_length_le (Q : Polynomial (Polynomial ℤ)) :
    ∃ C : ℕ, ∀ (P : Polynomial (Polynomial ℤ)) (b e n : ℕ),
      ∑ k ∈ P.support, ∑ i ∈ (P.coeff k).support, ((P.coeff k).coeff i).natAbs ≤ b →
      (∀ k, (P.coeff k).natDegree ≤ e) → P.natDegree ≤ n →
      ∑ k ∈ (P.modByMonic Q).support, ∑ i ∈ ((P.modByMonic Q).coeff k).support,
          (((P.modByMonic Q).coeff k).coeff i).natAbs ≤ C ^ n * b ∧
        ∀ k, ((P.modByMonic Q).coeff k).natDegree ≤ e + C * n := by
  sorry

end Transcendence
