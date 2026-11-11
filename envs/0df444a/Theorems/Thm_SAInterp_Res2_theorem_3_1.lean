-- Prove2me | Theorems.Thm_SAInterp_Res2_theorem_3_1
-- name    : SAInterp.Res2.theorem_3_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T22:37:34.790042+00:00
-- url     : https://prove2.me/theorems/cfeef590-fd0b-43d8-a75f-7631270717ba
-- title:
--   Theorem 3.1 — Lagrange interpolation; ω_k^{(d+1)} = ℓ_k(0) = (−1)^{k−1} C(d+1, k) and p(0) = Σ_k ω_k p(k) for deg p ≤ d
-- statement:
--   Let $t_1,\dots,t_{d+1}$ be distinct reals, and let $\ell_i(x)=\prod_{j\neq i}\frac{x-t_j}{t_i-t_j}$. Then every real polynomial $p$ of degree at most $d$ satisfies
--   $$p(z)=\sum_{i=1}^{d+1}p(t_i)\,\ell_i(z)\qquad\text{for all }z\in\mathbb R.$$
--   For the nodes $t_k=k$, the weights satisfy
--   $$\omega^{(d+1)}_k=\ell_k(0)=\prod_{j\neq k}\frac{-j}{k-j}=(-1)^{k-1}\binom{d+1}{k}\qquad(k=1,\dots,d+1),$$
--   and every real polynomial $p$ of degree at most $d$ satisfies $p(0)=\sum_{k=1}^{d+1}\omega^{(d+1)}_kp(k)$.
--
--   This is the interpolation identity behind every pseudoexpectation of the paper: $E_\mu$ evaluates at $0$ a polynomial whose values at $1,\dots,d+2$ are true expectations.
--
--   Differences from the source:
--   - reading: "for every degree ≤ d univariate polynomial p(z) ovek-j R" → over ℝ; reason: typesetting slip for "over R", as in the first clause (INSIGHTS I1).
--   - encoding: nodes t_1..t_{d+1} and the weight index k ∈ [d+1] → `Fin (d + 1)`, with node i ↦ i + 1; reason: Lean indexing, same instances.
--   - encoding: "degree ≤ d polynomial" and the polynomial identity p(z) = Σ p(t_i)ℓ_i(z) → `natDegree ≤ d` and equality of values at every real z; reason: Lean conventions, same statement (the zero polynomial is included on both sides).
-- source:
--   Acheampong, Davis, Robere, Polynomial Interpolation for Sherali-Adams Lower Bounds, STOC 2027 submission (manuscript sha256 8de0a787…), p. 23 (PDF p. 25), Theorem 3.1

import Mathlib
import Definitions.Def_SAInterp_Res2_Interp

open Polynomial

namespace SAInterp.Res2

/-- Theorem 3.1 (p. 23): Lagrange interpolation through `d + 1` distinct real nodes, the closed
form `ω_k^{(d+1)} = ℓ_k(0) = (−1)^{k−1} C(d+1, k)` for the nodes `1, …, d + 1`, and
`p(0) = ∑_{k=1}^{d+1} ω_k^{(d+1)} p(k)` for every real polynomial `p` of degree `≤ d`.
The node `k ∈ [d + 1]` is `k − 1 : Fin (d + 1)`. -/
theorem theorem_3_1 (d : ℕ) :
    (∀ t : Fin (d + 1) → ℝ, Function.Injective t → ∀ p : ℝ[X], p.natDegree ≤ d →
      ∀ z : ℝ, p.eval z = ∑ i, p.eval (t i) * (lagrangeBasis t i).eval z) ∧
    (∀ k : Fin (d + 1),
      omega (d + 1) (k.val + 1) =
          (lagrangeBasis (fun i : Fin (d + 1) => (i.val : ℝ) + 1) k).eval 0 ∧
        omega (d + 1) (k.val + 1) = (-1 : ℝ) ^ k.val * ((d + 1).choose (k.val + 1) : ℝ)) ∧
    (∀ p : ℝ[X], p.natDegree ≤ d →
      p.eval 0 = ∑ k ∈ Finset.Icc 1 (d + 1), omega (d + 1) k * p.eval (k : ℝ)) := by sorry

end SAInterp.Res2
