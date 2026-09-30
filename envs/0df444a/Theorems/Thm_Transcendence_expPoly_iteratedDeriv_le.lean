-- Prove2me | Theorems.Thm_Transcendence_expPoly_iteratedDeriv_le
-- name    : Transcendence.expPoly_iteratedDeriv_le
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-30T04:10:48.722492+00:00
-- url     : https://prove2.me/theorems/305d8079-de0f-43d6-9a80-299b0601e6d1
-- title:
--   The derivatives of an exponential polynomial at a point are bounded by its first N, geometrically in the order
-- statement:
--   Let $f(z) = \sum_{j} P_j(z)\,e^{w_j z}$, over a finite index set, with $|w_j| \le W$ and each $P_j$ zero or of degree less than $q_j$. Put $N = \sum_j q_j$. If $|f^{(s)}(c)| \le D$ for every $s < N$ at a point $c$, with $D \ge 0$, then for every $n$
--
--   $$|f^{(n)}(c)| \le D\,(W+1)^{n+N}.$$
--
--   The frequencies $w_j$ need not be distinct.
--
--   **Proof idea.** Induction on $N$. If $N = 0$, every $P_j$ is zero. Otherwise pick $j_0$ with $q_{j_0} \ge 1$ and peel that frequency: $g = f' - w_{j_0} f$ has the same shape, with $q_{j_0}$ lowered by one. Its first $N - 1$ derivatives at $c$ are at most $D(W+1)$, so by induction $|g^{(n)}(c)| \le D(W+1)^{n+N}$. Then $f^{(n+1)}(c) = g^{(n)}(c) + w_{j_0} f^{(n)}(c)$ gives the bound for $f$ by induction on $n$, because $D(W+1)^{n+N} + W\,D(W+1)^{n+N} = D(W+1)^{n+1+N}$.
--
--   **What it is for.** With the Taylor series at $c$ it gives `FourExp.expPoly_value_le_derivs` in a few lines, in place of the binomial bookkeeping of that node's first formal proof.
--
--   **Novelty.** None is claimed. The function $f$ satisfies the linear differential equation of order $N$ whose characteristic polynomial is $\prod_j (X - w_j)^{q_j}$, and the bound is the elementary induction along it.
-- source:
--   No source is claimed; an elementary induction. It is used in the second formal proof of FourExp.expPoly_value_le_derivs, whose estimate is M. Waldschmidt, Indépendance algébrique des valeurs de la fonction exponentielle, Bull. Soc. Math. France 99 (1971), 285–304, §4. Formal proof: Diaz modulus mission, 30 September 2026 (C. Perassi).

import Mathlib

open Finset Polynomial

namespace Transcendence

/-- Derivatives of an exponential polynomial `f(z) = ∑ⱼ Pⱼ(z) e^{wⱼ z}`, with `|wⱼ| ≤ W` and `deg Pⱼ < qⱼ`,
`∑ qⱼ = N`: if the first `N` derivatives at a point `c` are at most `D`, then
`‖f⁽ⁿ⁾(c)‖ ≤ D (W + 1)^{n + N}` for every `n`. -/
theorem expPoly_iteratedDeriv_le {ι : Type*} [Fintype ι] (w : ι → ℂ) (W : ℝ) (hW0 : 0 ≤ W)
    (hW : ∀ j, ‖w j‖ ≤ W) (c : ℂ) (N : ℕ) (q : ι → ℕ) (P : ι → ℂ[X])
    (hP : ∀ j, P j = 0 ∨ (P j).natDegree < q j) (hN : ∑ j, q j = N) (D : ℝ) (hD0 : 0 ≤ D)
    (hD : ∀ s < N, ‖iteratedDeriv s (fun z => ∑ j, (P j).eval z * Complex.exp (w j * z)) c‖ ≤ D)
    (n : ℕ) :
    ‖iteratedDeriv n (fun z => ∑ j, (P j).eval z * Complex.exp (w j * z)) c‖
      ≤ D * (W + 1) ^ (n + N) := by
  sorry

end Transcendence
