-- Prove2me | Theorems.Thm_VeinottWagnerSS_Bounds_lemma5_sLow_le_sn
-- name    : VeinottWagnerSS.Bounds.lemma5_sLow_le_sn
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T13:52:05.242869+00:00
-- url     : https://prove2.me/theorems/c32209f4-0088-49f9-a0dc-d0dbfbda53c0
-- title:
--   Lemma 5 — $\underline{s} \le s_n$ for an optimal n-period policy using $(s_n, S_n)$ in period 1
-- statement:
--   Consider the $n$-period inventory model with $n \ge 2$ under the standing assumptions ($0 \le \alpha \le 1$, $K \ge 0$, $\varphi$ with finite mean, $G_\alpha$ convex on $\mathbb Z$ with $G_\alpha(y) \to \infty$ as $|y| \to \infty$). Let $Y^n$ be an optimal policy which in period 1 uses the $(s_n, S_n)$ rule for some integers $s_n \le S_n$. Then
--   $$\underline{s} \le s_n,$$
--   where $\underline s$ is the smallest integer with $G_\alpha(\underline s) \le G_\alpha(\underline S) + K$.
--
--   This is the lower bound on the reorder point in Theorem 4(a).
--
--   **Formalization Note** Only the first-period rule of $Y^n$ is restricted; its later decisions may be arbitrary history-dependent functions.
-- source:
--   Veinott & Wagner, Computing Optimal (s, S) Inventory Policies, Management Sci. 11 (1965), p. 549, Appendix §2, Lemma 5

import Mathlib
import Definitions.Def_VeinottWagnerSS_Bounds_Model
import Definitions.Def_VeinottWagnerSS_Bounds_CriticalNumbers

open scoped ENNReal

namespace VeinottWagnerSS.Bounds

/-- Lemma 5, p. 549. Let `Y` be an optimal policy for the `n`-period model (`n ≥ 2`) that uses
the `(s_n, S_n)` rule (`s_n ≤ S_n`) in period 1. Then `s̲ ≤ s_n`. Later periods of `Y` are
unrestricted. -/
theorem lemma5_sLow_le_sn (G : ℤ → ℝ) (K α : ℝ) (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1) (hK : 0 ≤ K)
    (hconv : ∀ y : ℤ, G (y + 1) - G y ≤ G (y + 2) - G (y + 1))
    (hG_top : Filter.Tendsto G Filter.atTop Filter.atTop)
    (hG_bot : Filter.Tendsto G Filter.atBot Filter.atTop)
    (φ : PMF ℕ) (hμ : ∑' k : ℕ, (k : ℝ≥0∞) * φ k ≠ ⊤)
    (n : ℕ) (hn : 2 ≤ n)
    (Y : Policy) (sn Sn : ℤ) (hY : IsOptimal φ G K α n Y) (hsS : sn ≤ Sn)
    (hrule : UsesRule Y 0 sn Sn) :
    sLow G K ≤ sn := by sorry

end VeinottWagnerSS.Bounds
