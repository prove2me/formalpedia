-- Prove2me | Theorems.Thm_RobustKZClust_Main_lemma_4_4
-- name    : RobustKZClust.Main.lemma_4_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T05:11:35.174196+00:00
-- url     : https://prove2.me/theorems/cc07a46d-fdf5-438d-b056-c151bb1d5bdd
-- title:
--   Lemma 4.4 (Tensorization) — ‖F^d(c+u) − τ^r(c,u)‖ ≤ (2^r/r!)‖u‖^r and ‖τ^{[j]}_r(c,u)‖ ≤ (2^j/j!)‖u‖^j
-- statement:
--   Let $z\ge1$. Let $f:\mathbb R\to\ell_1(\mathbb Z)$ take values in probability vectors. For every $c\in\mathbb R$, let $b_0(c),\dots,b_{z-1}(c)\in\ell_1(\mathbb Z)$ satisfy $b_0(c)=f(c)$, $\|b_j(c)\|_1\le 2^j/j!$ for $j<z$, and $\|f(c+\delta)-\sum_{j<r}b_j(c)\delta^j\|_1\le(2^r/r!)|\delta|^r$ for all $1\le r\le z$ and $\delta\in\mathbb R$; these are (27) and (28) with $f$ in place of $f_z$. Let $F^d(x)=\bigotimes_{j=1}^d f(x_j)$.
--
--   For $c,u\in\mathbb R^d$ and an integer $1\le r\le z$, let $\tau^r(c,u)$ be the expansion of $\bigotimes_{j=1}^d\bigl(\sum_{k=0}^{r-1}b_k(c_j)u_j^k\bigr)$ with only the terms of total degree less than $r$ in $u$. Then
--
--   $$\|F^d(c+u)-\tau^r(c,u)\|_1\le\frac{2^r}{r!}\|u\|_1^r,\qquad(39)$$
--
--   and the homogeneous degree-$j$ part satisfies
--
--   $$\|\tau^{[j]}_r(c,u)\|_1\le\frac{2^j}{j!}\|u\|_1^j\quad(0\le j<r).\qquad(40)$$
--
--   With Lemma 4.3 this yields the order-$z$ Lipschitz approximation (8) of the hierarchical assignment in every dimension, with correction polynomials of total degree at most $z-1$.
--
--   Differences from the source:
--   - reading: ∥u∥ → the ℓ_1 norm Σ_i |u_i|; reason: the proof's last step (|u_1| + ∥u′∥)^r = ∥u∥^r and the target bound (8) use the ℓ_1 norm.
--   - encoding: f : R → ℓ_1(Z) with probability-vector values, b_j(c) ∈ ℓ_1(Z) → functions ℝ → ℤ → ℝ with nonnegative summable values of sum 1, and functions ℕ → ℝ → ℤ → ℝ absolutely summable for j < z; reason: Lean's sequences.
--   - generalization: d ≥ 1 → every d ∈ ℕ; reason: at d = 0 both sides are trivial (F^0 = τ^r = the unit vector), so the statement specializes to the source's d ≥ 1.
-- source:
--   Guo, Jiang, Krauthgamer, Xie, Zhou, Adversarially Robust Streaming Algorithms for (k, z)-Clustering, STOC 2027 submission (manuscript sha256 7d9aadba…), pp. 21–22, Lemma 4.4 (Tensorization), Eqs. (39)–(40); hypotheses p. 21 (f, b_j satisfying (27), (28))

import Mathlib
import Definitions.Def_RobustKZClust_Main_Spline

namespace RobustKZClust.Main

/-- Lemma 4.4 (Tensorization, pp. 21–22). Let `f : ℝ → ℓ_1(ℤ)` take values in probability
vectors and `b_0(c), …, b_{z−1}(c) ∈ ℓ_1(ℤ)` satisfy `b_0(c) = f(c)`, (27) and (28) with `f` in
place of `f_z`. Then for `c, u ∈ ℝ^d` and `1 ≤ r ≤ z`,
`‖F^d(c + u) − τ^r(c, u)‖_1 ≤ (2^r/r!) ‖u‖_1^r` (39) and
`‖τ^{[j]}_r(c, u)‖_1 ≤ (2^j/j!) ‖u‖_1^j` for `0 ≤ j < r` (40). -/
theorem lemma_4_4 (z : ℕ) (hz : 1 ≤ z) (f : ℝ → ℤ → ℝ) (b : ℕ → ℝ → ℤ → ℝ)
    (hf_nonneg : ∀ x v, 0 ≤ f x v) (hf_summ : ∀ x, Summable (f x))
    (hf_one : ∀ x, ∑' v, f x v = 1)
    (hb0 : ∀ c, b 0 c = f c)
    (h27 : ∀ c, ∀ j, j < z → InL1 (b j c) ∧ l1norm (b j c) ≤ 2 ^ j / (j.factorial : ℝ))
    (h28 : ∀ c, ∀ r : ℕ, 1 ≤ r → r ≤ z → ∀ δ : ℝ,
      l1norm (fun v => f (c + δ) v - ∑ j ∈ Finset.range r, b j c v * δ ^ j) ≤
        2 ^ r / (r.factorial : ℝ) * |δ| ^ r)
    (d : ℕ) (c u : Fin d → ℝ) (r : ℕ) (hr1 : 1 ≤ r) (hrz : r ≤ z) :
    l1norm (fun v => tensorVec f (c + u) v - tau b r c u v) ≤
        2 ^ r / (r.factorial : ℝ) * (∑ i, |u i|) ^ r ∧
    ∀ j, j < r → l1norm (tauHom b r j c u) ≤ 2 ^ j / (j.factorial : ℝ) * (∑ i, |u i|) ^ j := by sorry

end RobustKZClust.Main
