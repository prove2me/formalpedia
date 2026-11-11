-- Prove2me | Theorems.Thm_RobustKZClust_Main_lemma_4_3
-- name    : RobustKZClust.Main.lemma_4_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T05:11:36.682688+00:00
-- url     : https://prove2.me/theorems/4cab9e95-07fc-4b75-8908-32f0b7617f76
-- title:
--   Lemma 4.3 — Taylor coefficients of f_z in ℓ_1(ℤ) with ‖b_j‖ ≤ 2^j/j! and remainders (2^r/r!)|δ|^r
-- statement:
--   Let $z\ge1$ be an integer and $f_z(t)\in\ell_1(\mathbb Z)$ the probability vector of $\lfloor t-(V_1+\dots+V_z)\rfloor$, with $V_j$ independent and uniform on $[0,1)$. For every $c\in\mathbb R$ there are coefficient vectors $b_0(c),\dots,b_{z-1}(c)\in\ell_1(\mathbb Z)$ with $b_0(c)=f_z(c)$ such that
--
--   $$\|b_j(c)\|_1\le\frac{2^j}{j!}\quad(0\le j<z),\qquad(27)$$
--
--   and, simultaneously for every integer $1\le r\le z$ and every $\delta\in\mathbb R$,
--
--   $$\Bigl\|f_z(c+\delta)-\sum_{j=0}^{r-1}b_j(c)\,\delta^j\Bigr\|_1\le\frac{2^r}{r!}|\delta|^r.\qquad(28)$$
--
--   This one-dimensional Taylor estimate, tensorized by Lemma 4.4, gives the order-$z$ Lipschitz approximation property of the hierarchical assignment.
--
--   **Formalization Note.** The coefficient vectors are a sequence $b_0,b_1,\dots$ of functions $\mathbb Z\to\mathbb R$, and only $b_0,\dots,b_{z-1}$ are constrained or used.
--
--   Differences from the source:
--   - encoding: b_0(c), …, b_{z−1}(c) ∈ ℓ_1(Z) → functions ℤ → ℝ indexed by j ∈ ℕ, absolutely summable for j < z, the ℓ_1 norm as a tsum of absolute values; reason: Lean's sequences; the entries with j ≥ z are unused.
--   - encoding: Pr over V_1, …, V_z → Lebesgue measure restricted to [0,1)^z; reason: the law of independent uniforms.
-- source:
--   Guo, Jiang, Krauthgamer, Xie, Zhou, Adversarially Robust Streaming Algorithms for (k, z)-Clustering, STOC 2027 submission (manuscript sha256 7d9aadba…), p. 18, Lemma 4.3, Eqs. (27)–(28)

import Mathlib
import Definitions.Def_RobustKZClust_Main_Spline

namespace RobustKZClust.Main

/-- Lemma 4.3 (p. 18): for every `c ∈ ℝ` there are `b_0(c), …, b_{z−1}(c) ∈ ℓ_1(ℤ)` with
`b_0(c) = f_z(c)`, `‖b_j(c)‖_1 ≤ 2^j/j!` (27), and for every integer `1 ≤ r ≤ z` and `δ ∈ ℝ`,
`‖f_z(c + δ) − ∑_{j<r} b_j(c) δ^j‖_1 ≤ (2^r/r!) |δ|^r` (28). -/
theorem lemma_4_3 (z : ℕ) (hz : 1 ≤ z) (c : ℝ) :
    ∃ b : ℕ → ℤ → ℝ, b 0 = fvec z c ∧
      (∀ j, j < z → InL1 (b j) ∧ l1norm (b j) ≤ 2 ^ j / (j.factorial : ℝ)) ∧
      ∀ r : ℕ, 1 ≤ r → r ≤ z → ∀ δ : ℝ,
        l1norm (fun v => fvec z (c + δ) v - ∑ j ∈ Finset.range r, b j v * δ ^ j) ≤
          2 ^ r / (r.factorial : ℝ) * |δ| ^ r := by sorry

end RobustKZClust.Main
