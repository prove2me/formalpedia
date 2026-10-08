-- Prove2me | Theorems.Thm_WhittleGittins_Retirement_retirement_case
-- name    : WhittleGittins.Retirement.retirement_case
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:55:39.991993+00:00
-- url     : https://prove2.me/theorems/30e4c66d-087a-432b-ad01-df44222b87e8
-- title:
--   Proof of Theorem 1, retirement case — if maxⱼ Mⱼ ≤ M then F̂(x, s, M) = M ≥ LᵢF̂
-- statement:
--   In Whittle's bandit process with per-project horizons $s$, let $\hat F$ be defined by (13), $L_i\hat F$ by (15) and $M_j = M_j(x_j, s_j)$ be the index of project $j$. If
--   $$\max_j M_j \le M,$$
--   the maximum being over the projects with $s_j > 0$, then
--   $$\hat F(x, s, M) = M,$$
--   and $M \ge L_i\hat F(x, s, M)$ for every project $i$ with $s_i > 0$. Thus $\hat F$ satisfies the dynamic programming equation (16) with $\hat F = M$, corresponding to adoption of the retirement option.
--
--   Together with (21) this covers both branches of the index rule in the inductive proof of Theorem 1.
--
--   **Formalization Note** Projects with $s_j = 0$ (index $-\infty$) impose no condition. Projects are indexed by `Fin N`.
-- source:
--   Whittle, Multi-armed Bandits and the Gittins Index, J. R. Statist. Soc. B 42 (1980), p. 148 (PDF 6), Section 4, proof of Theorem 1, retirement case

import Mathlib
import Definitions.Def_WhittleGittins_Retirement_BanditProcess

namespace WhittleGittins.Retirement

open MeasureTheory ProbabilityTheory

/-- Retirement case of the proof of Theorem 1 (p. 148): if `maxⱼ Mⱼ ≤ M` (over the active
projects) then `F̂(x, s, M) = M`, and `M ≥ Lᵢ F̂` for every active `i`, so `F̂` satisfies (16)
with the retirement option. -/
theorem retirement_case {N : ℕ} {X : Fin N → Type*} [∀ i, MeasurableSpace (X i)]
    (B : BanditProcess N X) (x : ∀ j, X j) (s : Fin N → ℕ) (M : ℝ)
    (hM : ∀ j, 0 < s j → index B j (x j) (s j) ≤ M) :
    Fhat B x s M = M ∧ ∀ i, 0 < s i → LFhat B i x s M ≤ M := by sorry

end WhittleGittins.Retirement
