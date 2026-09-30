-- Prove2me | Theorems.Thm_VeinottWagnerSS_Bounds_lemma2_SLow_le_Sn
-- name    : VeinottWagnerSS.Bounds.lemma2_SLow_le_Sn
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T13:41:01.525566+00:00
-- url     : https://prove2.me/theorems/6cda7e1d-ee5e-4f3e-916e-60529f3d325c
-- title:
--   Lemma 2 — $\underline{S} \le S_n$ for an optimal n-period policy using $(s_n, S_n)$ in period 1
-- statement:
--   Consider the $n$-period inventory model with $n \ge 2$, discount factor $0 \le \alpha \le 1$, set-up cost $K \ge 0$, a demand distribution $\varphi$ on $\{0, 1, \dots\}$ with finite mean, and a one-period cost $G_\alpha : \mathbb Z \to \mathbb R$ that is convex on the integers with $G_\alpha(y) \to \infty$ as $|y| \to \infty$. Let $Y^n$ be an optimal policy for this model which in period 1 uses the $(s_n, S_n)$ rule for some integers $s_n \le S_n$. Then
--   $$\underline{S} \le S_n,$$
--   where $\underline{S}$ is the smallest minimizer of $G_\alpha$.
--
--   This is the first of the four comparison lemmas behind Theorem 4(a): an optimal first-period order-up-to level is never below the single-period optimum.
--
--   **Formalization Note** Only the first-period rule of $Y^n$ is restricted; its later decisions may be arbitrary (history-dependent) functions of the past, and optimality is against all admissible policies for every initial level.
-- source:
--   Veinott & Wagner, Computing Optimal (s, S) Inventory Policies, Management Sci. 11 (1965), p. 547, Appendix §2, Lemma 2

import Mathlib
import Definitions.Def_VeinottWagnerSS_Bounds_Model
import Definitions.Def_VeinottWagnerSS_Bounds_CriticalNumbers

open scoped ENNReal

namespace VeinottWagnerSS.Bounds

/-- Lemma 2, p. 547. Let `Y` be an optimal policy for the `n`-period model (`n ≥ 2`) that uses
the `(s_n, S_n)` rule (`s_n ≤ S_n`) in period 1. Then `S̲ ≤ S_n`. Later periods of `Y` are
unrestricted. -/
theorem lemma2_SLow_le_Sn (G : ℤ → ℝ) (K α : ℝ) (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1) (hK : 0 ≤ K)
    (hconv : ∀ y : ℤ, G (y + 1) - G y ≤ G (y + 2) - G (y + 1))
    (hG_top : Filter.Tendsto G Filter.atTop Filter.atTop)
    (hG_bot : Filter.Tendsto G Filter.atBot Filter.atTop)
    (φ : PMF ℕ) (hμ : ∑' k : ℕ, (k : ℝ≥0∞) * φ k ≠ ⊤)
    (n : ℕ) (hn : 2 ≤ n)
    (Y : Policy) (sn Sn : ℤ) (hY : IsOptimal φ G K α n Y) (hsS : sn ≤ Sn)
    (hrule : UsesRule Y 0 sn Sn) :
    SLow G ≤ Sn := by sorry

end VeinottWagnerSS.Bounds
