-- Prove2me | Theorems.Thm_ProportionalGroupDivision_Main_theorem_6
-- name    : ProportionalGroupDivision.Main.theorem_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:14:07.451486+00:00
-- url     : https://prove2.me/theorems/fae9e2fe-a660-4df9-ae75-56e86212e84b
-- title:
--   Theorem 6 (Top-down Beck–Fiala) — $|\langle A_i,x_0-x\rangle|\le C\log_2(4\max\{1,n/\Delta_n\})\sqrt{\Delta_i\log_2(4\Delta_1/\Delta_n)}$
-- statement:
--   There is an absolute constant $C>0$ such that the following holds. Let $\Delta_1\ge\Delta_2\ge\dots\ge\Delta_n>0$ be reals, let $A\in[0,1]^{n\times m}$ be $(\Delta_i)$-structured and let $x_0\in[0,1]^m$. Then there is $x\in\{0,1\}^m$ such that for all $1\le i\le n$
--
--   $$|\langle A_i,x_0-x\rangle|\ \le\ C\log_2\!\big(4\max\{1,n/\Delta_n\}\big)\cdot\sqrt{\Delta_i\log_2(4\Delta_1/\Delta_n)}.$$
--
--   The constant $C$ is chosen before $n$, $m$, the $\Delta_i$, $A$ and $x_0$. With $\Xi(s,r)=C\log_2(4s)\sqrt{\log_2(4r)}$ the bound reads $\Xi(\max\{1,n/\Delta_n\},\Delta_1/\Delta_n)\sqrt{\Delta_i}$; it is the paper's discrepancy bound for the nonuniform generalization of the Beck–Fiala problem, restated as Theorem 22.
--
--   Differences from the source:
--   - encoding: rows, agents and goods indexed 1, …, n → 0-based indices Fin n; agent (i, j) is a dependent pair with j : Fin (n i); reason: relabelling; changes no instance
-- source:
--   Alexander Shekhovtsov, Georgy Sokolov, Mikhail Cherniavskii, Andrey Kupavskii, Nearly Tight Bounds for Proportional Group Fair Divisions and One-Sided Discrepancy, STOC 2027 submission #606 (October 2026), PDF SHA-256 b01bf42964a30eaf9c85a3d02713fc0ac4cd63ae8653853fa44b062c0220f39a, Theorem 6, PDF p. 5 = printed p. 5; restated as Theorem 22, PDF p. 20

import Mathlib
import Definitions.Def_ProportionalGroupDivision_Main_Structured

namespace ProportionalGroupDivision.Main

/-- Theorem 6 (Bound on the Top-down Beck–Fiala problem, PDF p. 5; restated as Theorem 22, p. 20):
there is an absolute constant `C > 0` such that for every sequence of reals
`Δ_1 ≥ Δ_2 ≥ ⋯ ≥ Δ_N > 0`, every `(Δ_i)`-structured `A ∈ [0,1]^{N×m}` and every `x₀ ∈ [0,1]^m`
there is `x ∈ {0,1}^m` with, for all `1 ≤ i ≤ N`,
`|⟨A_i, x₀ − x⟩| ≤ C log₂(4 max{1, N/Δ_N}) · √(Δ_i log₂(4Δ_1/Δ_N))`
(the property `TopDownBound C`, chosen before `N, m, Δ, A, x₀`). -/
theorem theorem_6 : ∃ C : ℝ, 0 < C ∧ TopDownBound C := by sorry

end ProportionalGroupDivision.Main
