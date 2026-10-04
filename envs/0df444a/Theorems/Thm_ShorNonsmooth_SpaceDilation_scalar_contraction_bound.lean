-- Prove2me | Theorems.Thm_ShorNonsmooth_SpaceDilation_scalar_contraction_bound
-- name    : ShorNonsmooth.SpaceDilation.scalar_contraction_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-03T23:54:39.115681+00:00
-- url     : https://prove2.me/theorems/7e33a405-2b19-4337-bdc3-726947596db9
-- title:
--   Eq. (3.20) — the scalar contraction behind the SDG distance invariant
-- statement:
--   Let `M > N > 0` be real, `D ≥ 0`, `P` with `N*D ≤ P ≤ M*D`, and `a` with `1 ≤ a` and `a*(M - N) ≤ M + N`. Then
--
--   $$
--   a^2 \left(P - \frac{2MN}{M+N} D\right)^2 \le P^2 .
--   $$
--
--   This is the scalar contraction coefficient condition (3.20) of Shor (1985), Theorem 3.3, isolated from the SDG iteration.
--
--   Why it is the right estimate. Put $c = 2MN/(M+N)$. Since $P \ge N D \ge 0$, the claim is equivalent to $|a (P - c D)| \le P$, i.e. to the pair of linear inequalities
--
--   $$a(P - cD) \le P \quad\text{ and }\quad a(P - cD) \ge -P,$$
--
--   that is $(a-1) P \le a c D$ and $(a+1) P \ge a c D$. The first follows from $P \le M D$ provided $(a-1)(M+N) \le 2aN$, and the second from $P \ge N D$ provided $(a+1)(M+N) \ge 2aM$. Each of those two conditions is equivalent to the same single inequality
--
--   $$a (M - N) \le M + N,$$
--
--   which is precisely $a \le \frac{M+N}{M-N}$, the coefficient condition (3.20).
--
--   Sharpness. At $a = \frac{M+N}{M-N}$ the bound is an equality at both endpoints $P = N D$ and $P = M D$, so no larger coefficient can be allowed. For example, with $M = 2, N = 1, D = 1$ one has $c = 4/3$ and $P^2 - a^2 (P - cD)^2 = 0$ both at $P = 1$ and at $P = 2$.
--
--   Role in Theorem 3.3. Writing $u_k = A_k (x_k - x^*)$, $P_k = \langle \tilde g_k, u_k\rangle$ and $D_k = f(x_k) - f(x^*)$, the SDG recursion satisfies
--
--   $$\|u_{k+1}\|^2 - \|u_k\|^2 = \frac{a^2 (P_k - c D_k)^2 - P_k^2}{\|\tilde g_k\|^2},$$
--
--   so this lemma makes $\|u_{k+1}\| \le \|u_k\|$, i.e. the invariant $\|A_k (x_k - x^*)\| \le d$ of Theorem 3.3.
-- source:
--   Shor, Minimization Methods for Non-Differentiable Functions, Springer 1985, pp. 56-57, Theorem 3.3, conditions (3.18)-(3.20); the contraction coefficient analysis of p. 57.

import Mathlib

namespace ShorNonsmooth.SpaceDilation

/-- The scalar estimate (3.20) behind the SDG distance invariant of Theorem 3.3.

Let `0 < N ≤ M`, `0 ≤ D`, `N*D ≤ P ≤ M*D`, `1 ≤ a` and `a*(M - N) ≤ M + N`, i.e.
exactly the coefficient condition `1 < a ≤ (M+N)/(M-N)` of (3.20). Then

`a^2 * (P - 2MN/(M+N)*D)^2 ≤ P^2`.

This is the only analytic input the one-step estimate of Theorem 3.3 needs. Writing
`c = 2MN/(M+N)`, the goal is `|a*(P - c D)| ≤ P` for `P ≥ 0`, which splits into the two
linear halves

`a*(P - c D) ≤ P  ⟺  (a - 1)*P ≤ a*c*D`  (using `P ≤ M D`), and
`a*(P - c D) ≥ -P ⟺ (a + 1)*P ≥ a*c*D` (using `P ≥ N D`).

After clearing the positive factor `M*(M+N)` resp. `N*(M+N)` each half is denominator-free
and each is equivalent to the single hypothesis `a*(M - N) ≤ M + N`:

upper half  ⟺  (a - 1)*(M + N) ≤ 2*a*N  ⟺  a*(M - N) ≤ M + N,
lower half  ⟺  (a + 1)*(M + N) ≥ 2*a*M  ⟺  a*(M - N) ≤ M + N.

Squaring the two-sided estimate yields the claim. -/
theorem scalar_contraction_bound {M N D P a : ℝ} (hN : 0 < N) (hNM : N ≤ M)
    (hD : 0 ≤ D) (hlo : N * D ≤ P) (hhi : P ≤ M * D) (ha1 : 1 ≤ a)
    (haMN : a * (M - N) ≤ M + N) :
    a ^ 2 * (P - 2 * M * N / (M + N) * D) ^ 2 ≤ P ^ 2 := by sorry

end ShorNonsmooth.SpaceDilation
