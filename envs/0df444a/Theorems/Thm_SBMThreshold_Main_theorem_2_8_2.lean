-- Prove2me | Theorems.Thm_SBMThreshold_Main_theorem_2_8_2
-- name    : SBMThreshold.Main.theorem_2_8_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:17:29.508438+00:00
-- url     : https://prove2.me/theorems/7424d148-4368-40e3-8b6f-2f36e79b90c6
-- title:
--   Theorem 2.8 (2), p. 5 — E[Y²_{u,v} | σ_U] ≤ (1 + o(1)) 2 (s²/(s² − d))² s^{2k}/n² (square as in (17))
-- statement:
--   Under the hypotheses of Theorem 2.8 (Assumption 2.7; $s_n^2/d_n\ge\lambda>1$; $\alpha>0$ with $n^2d_n^{\alpha\log n}\le s_n^{2\alpha\log n}$; $k=\lceil\alpha\log n\rceil$), for every sequence $e_n\to0$ there is a sequence $c_n\to0$ such that, for all $n$, all distinct $u,v$, all $U\ni u,v$ with $|U|\le n^{e_n}$ and all labellings $\tau$,
--   $$
--   \mathbb E[Y_{u,v}^2\mid\sigma_U=\tau_U]\le(1+c_n)\cdot2\Bigl(\frac{s^2}{s^2-d}\Bigr)^2\frac{s^{2k}}{n^2}.
--   $$
--
--   Together with display (1) this shows that $Y_{u,v}$ has standard deviation of the same order as its mean $s^k/n$, so a bounded-away-from-zero fraction of its sign agrees with $\sigma_u\sigma_v$.
--
--   **Formalization Note** The page prints the first power of $s^2/(s^2-d)$. The proof's display (17), p. 25, gives $\sum_{i,j\ge0}(d/s^2)^{i+j}=(s^2/(s^2-d))^2$, and the leading term is really of that order, so the printed form fails when $d<s^2<2d$; this item states the square. The uniformity convention is that of Theorem 2.8 (1).
-- source:
--   Mossel, Neeman and Sly, A Proof of the Block Model Threshold Conjecture, arXiv:1311.4115v4, p. 5, Theorem 2.8, display (2), corrected by display (17), p. 25

import Mathlib
import Definitions.Def_SBMThreshold_Main_Setting
import Definitions.Def_SBMThreshold_Main_Paths
open Filter Topology Finset

namespace SBMThreshold.Main

/-- Theorem 2.8 (2) (p. 5), with the square that the proof's display (17), p. 25, gives:
uniformly over distinct `u, v`, sets `U ⊇ {u, v}` of size at most `n^{o(1)}` and labellings of `U`,
`E[Y_{u,v}² | σ_U] ≤ (1 + o(1)) · 2 · (s²/(s² - d))² · s^{2k} / n²` with `k = ⌈α log n⌉`. -/
theorem theorem_2_8_2 (a b : ℕ → ℝ) (ℓ : ℕ → ℕ) (lam α : ℝ)
    (hA : Assumption27 a b ℓ) (hP : Theorem28Params a b lam α) :
    ∀ e : ℕ → ℝ, Tendsto e atTop (𝓝 0) →
      ∃ c : ℕ → ℝ, Tendsto c atTop (𝓝 0) ∧
        ∀ (n : ℕ) (u v : Fin n) (U : Finset (Fin n)) (τ : Fin n → Bool),
          u ≠ v → u ∈ U → v ∈ U → (U.card : ℝ) ≤ (n : ℝ) ^ (e n) →
          condExp n (a n) (b n) U τ
              (fun _ G => pathY n (a n) (b n) (pathLen α n) u v G ^ 2) ≤
            (1 + c n) * 2 *
              (sPar (a n) (b n) ^ 2 / (sPar (a n) (b n) ^ 2 - dPar (a n) (b n))) ^ 2 *
              (sPar (a n) (b n) ^ (2 * pathLen α n) / (n : ℝ) ^ 2) := by sorry

end SBMThreshold.Main
