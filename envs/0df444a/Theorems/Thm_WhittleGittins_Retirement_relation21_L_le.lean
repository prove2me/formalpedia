-- Prove2me | Theorems.Thm_WhittleGittins_Retirement_relation21_L_le
-- name    : WhittleGittins.Retirement.relation21_L_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:55:32.983005+00:00
-- url     : https://prove2.me/theorems/6fdd3548-21ff-45d3-8e29-ca941959bff0
-- title:
--   Relation (21) — F̂ ≥ LᵢF̂, with equality if M ≤ Mᵢ and M₍ᵢ₎ ≤ Mᵢ
-- statement:
--   In Whittle's bandit process with per-project horizons $s$, let $\hat F(x, s, M)$ be defined by (13), and let
--   $$L_i\hat F(x, s, M) = R_i(x_i) + \beta\, \mathbb E\big[\hat F(x(t+1), D_i s, M) \mid x(t) = x,\ i(t) = i\big]$$
--   be the extended operator (15), where $D_i s$ lowers $s_i$ by one. Let $M_j = M_j(x_j, s_j)$ be the index of project $j$, and $M_{(i)} = \max_{j \ne i} M_j$ over the other active projects. Then for every project $i$ with $s_i > 0$,
--   $$\hat F \ge L_i \hat F, \qquad (21)$$
--   with equality if $M \le M_i$ and $M_{(i)} \le M_i$, that is, if $M_i = \max_j M_j \ge M$.
--
--   Relation (21) shows that engaging a project of maximal index is optimal in the dynamic programming equation (16) satisfied by $\hat F$.
--
--   **Formalization Note** The inequality is stated for active projects ($s_i > 0$) only, since an exhausted project cannot be engaged. The condition $M_{(i)} \le M_i$ is written as $M_j \le M_i$ for every other active project $j$. Projects are indexed by `Fin N`.
-- source:
--   Whittle, Multi-armed Bandits and the Gittins Index, J. R. Statist. Soc. B 42 (1980), p. 148 (PDF 6), Section 4, relation (21)

import Mathlib
import Definitions.Def_WhittleGittins_Retirement_BanditProcess

namespace WhittleGittins.Retirement

open MeasureTheory ProbabilityTheory

/-- Relation (21) (p. 148): for every active project `i`, `F̂ ≥ Lᵢ F̂`, with equality if
`M ≤ Mᵢ` and `M₍ᵢ₎ ≤ Mᵢ` (i.e. `Mᵢ` is maximal among the indices of the active projects). -/
theorem relation21_L_le {N : ℕ} {X : Fin N → Type*} [∀ i, MeasurableSpace (X i)]
    (B : BanditProcess N X) (x : ∀ j, X j) (s : Fin N → ℕ) (M : ℝ) (i : Fin N) (hi : 0 < s i) :
    LFhat B i x s M ≤ Fhat B x s M ∧
      (M ≤ index B i (x i) (s i) →
        (∀ j, j ≠ i → 0 < s j → index B j (x j) (s j) ≤ index B i (x i) (s i)) →
        LFhat B i x s M = Fhat B x s M) := by sorry

end WhittleGittins.Retirement
