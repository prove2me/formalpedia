-- Prove2me | Theorems.Thm_ProxFlatIP_theorem_2
-- name    : ProxFlatIP.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:14:35.867026+00:00
-- url     : https://prove2.me/theorems/8319adb6-cf25-46f9-be9d-9ffbc3126b13
-- title:
--   Theorem 2 — an optimal LP vertex lies strictly within $\ell_\infty$-distance $\frac{4n+2}{9}\Delta_{n-1}(A)$ of an optimal integer solution
-- statement:
--   Let $A\in\mathbb Z^{m\times n}$ be an integral matrix of full column rank, let $n\ge2$, $b\in\mathbb Z^m$ and $c\in\mathbb Q^n$. Let $x^*$ be an optimal vertex of $\mathrm{LP}(A,b,c)$. If $\mathrm{IP}(A,b,c)$ is feasible, then there exists an optimal solution $z^*$ of $\mathrm{IP}(A,b,c)$ such that
--   $$\|x^*-z^*\|_\infty<\frac{4n+2}{9}\cdot\Delta_{n-1}(A).$$
--
--   This improves the bound $n\cdot\Delta_{n-1}(A)$ of Cook, Gerards, Schrijver and Tardos for integral right-hand sides. For rational right-hand sides the improvement is false.
--
--   Differences from the source: none.
-- source:
--   Celaya, Kuhlmann, Paat, Weismantel, Proximity and flatness bounds for linear integer optimization, arXiv:2211.14941v1 [math.OC] (preprint, 27 Nov 2022), https://arxiv.org/abs/2211.14941v1, Theorem 2, p.2

import Mathlib
import Definitions.Def_ProxFlatIP_Minors

open Matrix

namespace ProxFlatIP

/-- **Theorem 2** (Celaya–Kuhlmann–Paat–Weismantel, *Proximity and flatness bounds for linear integer
optimization*, arXiv:2211.14941v1, Theorem 2, p.2). Let `A ∈ ℤ^{m×n}` have full column rank, `n ≥ 2`,
`b ∈ ℤᵐ`, `c ∈ ℚⁿ`, and let `x*` be an optimal vertex of `LP(A,b,c)`. If `IP(A,b,c)` is feasible, there
is an optimal solution `z*` of `IP(A,b,c)` with `‖x* − z*‖_∞ < ((4n+2)/9) Δ_{n−1}(A)`.

**Formalization Note.** `‖·‖` on `Fin n → ℝ` is Mathlib's sup norm, which is `‖·‖_∞`. `Δ_{n−1}(A)` is
the largest absolute minor of order exactly `n − 1` (`minorMax`). -/
theorem theorem_2 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (hA : FullColRank A) (hn : 2 ≤ n)
    (b : Fin m → ℤ) (c : Fin n → ℚ) (xs : Fin n → ℝ) (hxs : IsLPOptimalVertex A b c xs)
    (hIP : IsIPFeasible A b) :
    ∃ zs : Fin n → ℝ, IsIPOptimal A b c zs ∧
      ‖xs - zs‖ < (4 * (n : ℝ) + 2) / 9 * (minorMax (n - 1) A : ℝ) := by sorry

end ProxFlatIP
