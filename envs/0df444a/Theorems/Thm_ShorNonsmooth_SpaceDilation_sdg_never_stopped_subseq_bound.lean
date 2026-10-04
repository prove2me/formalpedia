-- Prove2me | Theorems.Thm_ShorNonsmooth_SpaceDilation_sdg_never_stopped_subseq_bound
-- name    : ShorNonsmooth.SpaceDilation.sdg_never_stopped_subseq_bound
-- status  : Open
-- author  : @WillR
-- created : 2026-10-03T23:18:02.186865+00:00
-- url     : https://prove2.me/theorems/4691aa9d-810d-4809-9e1d-cfbc9ae18e40
-- title:
--   Theorem 3.1 for never-stopping runs — transformed gradients decay along a subsequence
-- statement:
--   Under the hypotheses of Theorem 3.1, if the SDG run never triggers the stopping rule $g(x_k) = 0$, then there are $c > 0$ and $k_0 < k_1 < \cdots$ with $\|\tilde g_{k_p}\| < c\,(\prod_{j\le k_p}\alpha_j)^{-1/n}$. This is the determinant-trace-liminf core of the proof; the complementary case (stopped run, where the state freezes and $\tilde g \equiv 0$ from then on) is immediate.
-- source:
--   Shor, Minimization Methods for Non-Differentiable Functions, Springer 1985, proof of Theorem 3.1, p. 53, main (never-stopping) case: determinant growth against trace control forces the transformed gradients below the geometric rate infinitely often.

import Mathlib
import Definitions.Def_ShorNonsmooth_SpaceDilation_SDGMethod

namespace ShorNonsmooth.SpaceDilation

/-- Shor (1985), proof of Theorem 3.1, p. 53, main case. Along an SDG run that never triggers the stopping rule `g(x_k) = 0`, the determinant-trace argument applies: `det A_k = (∏ α_j) det A_0` grows geometrically while `tr (A_k^* A_k)` grows at most like the convergent geometric-weighted sum of `‖g̃_j‖^{-2}`, forcing `‖g̃_j‖ < c (∏ α)^{-1/n}` at arbitrarily large indices, hence along a subsequence. The complementary stopped case (some `g(x_J) = 0`, after which the state freezes and `g̃ ≡ 0`) is immediate. -/
theorem sdg_never_stopped_subseq_bound {n : ℕ} (hn : 0 < n)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (h : ℕ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → ℝ) (α : ℕ → ℝ)
    (x₀ : EuclideanSpace ℝ (Fin n))
    (B₀ : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (d αstar δ : ℝ) (hd : 0 < d) (hαstar : 0 < αstar) (hδ : 0 < δ)
    (hg : ∀ k : ℕ, ‖g (sdg g h α x₀ B₀ k).x‖ ≤ d)
    (hα : ∀ k : ℕ, 1 ≤ k → 1 + δ ≤ α k ∧ α k ≤ αstar)
    (hnever : ∀ j : ℕ, g (sdg g h α x₀ B₀ j).x ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∃ kp : ℕ → ℕ, StrictMono kp ∧
      ∀ p : ℕ, ‖gTilde g h α x₀ B₀ (kp p)‖ <
        c * (∏ j ∈ Finset.Icc 1 (kp p), α j) ^ (-(1 : ℝ) / n) := by sorry

end ShorNonsmooth.SpaceDilation
