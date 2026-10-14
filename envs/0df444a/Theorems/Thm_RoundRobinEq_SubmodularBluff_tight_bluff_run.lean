-- Prove2me | Theorems.Thm_RoundRobinEq_SubmodularBluff_tight_bluff_run
-- name    : RoundRobinEq.SubmodularBluff.tight_bluff_run
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:18:56.533114+00:00
-- url     : https://prove2.me/theorems/18609edb-2194-41de-adea-51f0a4c5e4a0
-- title:
--   §3.2, p. 13, proof of Theorem 3.7 — tight instance: the bluff order is g_1 > ⋯ > g_5 and the bluff run gives A_1 = {g_1, g_3, g_5}, A_2 = {g_2, g_4}
-- statement:
--   Consider the tight instance of Theorem 3.7 with $0<\varepsilon_1<\varepsilon_2<\varepsilon_3<1$ (additive agent 1, OXS agent 2, and a dummy good $g_6$). Then:
--
--   1. $g_1\succ g_2\succ g_3\succ g_4\succ g_5\succ g_6$ is an output of Algorithm 2, so the profile in which both agents report it is a bluff profile;
--   2. Round-Robin on this profile gives agent 1 the bundle $A_1=\{g_1,g_3,g_5\}$ and agent 2 the bundle $A_2=\{g_2,g_4,g_6\}$;
--   3. $$v_1(A_1)=4-\varepsilon_1-\varepsilon_3,\qquad v_2(A_2)=1.$$
--
--   Together with agent 2's deviation, this shows that the factor $\tfrac12$ of Theorem 3.7 cannot be improved.
--
--   **Formalization Note.** Goods $g_\ell$ are `ℓ - 1 : Fin 6` and agents 1, 2 are `0, 1 : Fin 2`. The dummy good $g_6$ (value $0$) comes from the paper's standing convention $m=kn$ (p. 7) and ends up in $A_2$ without changing any value. The order $g_1\succ\cdots\succ g_6$ is the one Algorithm 2 produces with lexicographic tie-breaking (agent 2 is indifferent among $g_4,g_5,g_6$ at her second turn). The paper's "$1\gg\varepsilon_3>\varepsilon_2>\varepsilon_1>0$" is encoded as $0<\varepsilon_1<\varepsilon_2<\varepsilon_3<1$, under which all three claims hold.
-- source:
--   Amanatidis et al., Round-Robin Beyond Additive Agents, arXiv:2301.13652v1, p. 13, proof of Theorem 3.7 (tight instance, bluff run)

import Mathlib
import Definitions.Def_RoundRobinEq_SubmodularBluff_Setting
import Definitions.Def_RoundRobinEq_SubmodularBluff_Bluff
import Definitions.Def_RoundRobinEq_SubmodularBluff_TightInstance

namespace RoundRobinEq.SubmodularBluff

theorem tight_bluff_run (ε₁ ε₂ ε₃ : ℝ) (h₁ : 0 < ε₁) (h₁₂ : ε₁ < ε₂) (h₂₃ : ε₂ < ε₃)
    (h₃ : ε₃ < 1) :
    IsGreedyOrder (tightVal ε₁ ε₂ ε₃) tightBluffOrder ∧
      RoundRobinEq.CancelableBluff.roundRobin (bluff tightBluffOrder : Fin 2 → List (Fin 6)) 0 = {0, 2, 4} ∧
      RoundRobinEq.CancelableBluff.roundRobin (bluff tightBluffOrder : Fin 2 → List (Fin 6)) 1 = {1, 3, 5} ∧
      tightVal ε₁ ε₂ ε₃ 0 {0, 2, 4} = 4 - ε₁ - ε₃ ∧
      tightVal ε₁ ε₂ ε₃ 1 {1, 3, 5} = 1 := by sorry

end RoundRobinEq.SubmodularBluff
