-- Prove2me | Theorems.Thm_RoundRobinEq_SubmodularBluff_tight_deviation
-- name    : RoundRobinEq.SubmodularBluff.tight_deviation
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T01:19:08.060574+00:00
-- url     : https://prove2.me/theorems/f7b79165-2313-462a-bb11-aaa8157cd2ad
-- title:
--   §3.2, pp. 13–14, proof of Theorem 3.7 — tight instance: agent 2’s best deviation value is 2 − ε_1 − ε_2, attained by g_3 > g_4 > g_1 > g_2 > g_5
-- statement:
--   Consider the tight instance of Theorem 3.7 with $0<\varepsilon_1<\varepsilon_2<\varepsilon_3\le 1/2$, and let agent 1 report the bluff order $g_1\succ g_2\succ\cdots\succ g_6$. Then (i) whatever ranking $\succ_2$ agent 2 reports, the bundle $A_2(\succ_2)$ she receives from Round-Robin satisfies
--   $$v_2(A_2(\succ_2))\le 2-\varepsilon_1-\varepsilon_2,$$
--   and (ii) this maximum is attained: if agent 2 reports
--   $$g_3\succ g_4\succ g_1\succ g_2\succ g_5\succ g_6,$$
--   which is a ranking, then Round-Robin gives her the goods $\{g_3,g_4,g_6\}$ and $v_2(\{g_3,g_4,g_6\})=2-\varepsilon_1-\varepsilon_2$.
--
--   Since $v_2(A_2)=1$ in the bluff run, agent 2 improves her value by a factor $2-\varepsilon_1-\varepsilon_2$, which tends to $2$ as the $\varepsilon$'s vanish.
--
--   **Formalization Note.** The page assumes $1\gg\varepsilon_3>\varepsilon_2>\varepsilon_1>0$; here "$1\gg\varepsilon_3$" is read as $\varepsilon_3\le 1/2$. Some such quantitative reading is needed for the maximum: agent 2’s best deviation value is $\max\{1,\,2-\varepsilon_1-\varepsilon_2\}$, so the maximum claim fails when $\varepsilon_1+\varepsilon_2>1$ (e.g. $0.6,0.7,0.8$), and $\varepsilon_3\le 1/2$ rules this out. The dummy good $g_6$ is the paper's device for $m=kn$ (p. 7).
-- source:
--   Amanatidis et al., Round-Robin Beyond Additive Agents, arXiv:2301.13652v1, pp. 13–14, proof of Theorem 3.7 (tight instance, agent 2's deviation)

import Mathlib
import Definitions.Def_RoundRobinEq_SubmodularBluff_Setting
import Definitions.Def_RoundRobinEq_SubmodularBluff_Bluff
import Definitions.Def_RoundRobinEq_SubmodularBluff_TightInstance

namespace RoundRobinEq.SubmodularBluff

theorem tight_deviation (ε₁ ε₂ ε₃ : ℝ) (h₁ : 0 < ε₁) (h₁₂ : ε₁ < ε₂) (h₂₃ : ε₂ < ε₃)
    (h₃ : ε₃ ≤ 1 / 2) :
    (∀ τ : List (Fin 6), RoundRobinEq.CancelableBluff.IsRanking τ →
      tightVal ε₁ ε₂ ε₃ 1 (RoundRobinEq.CancelableBluff.roundRobin (Function.update (bluff tightBluffOrder : Fin 2 → List (Fin 6)) 1 τ) 1) ≤ 2 - ε₁ - ε₂) ∧
    RoundRobinEq.CancelableBluff.IsRanking tightDeviation ∧
      RoundRobinEq.CancelableBluff.roundRobin (Function.update (bluff tightBluffOrder : Fin 2 → List (Fin 6)) 1 tightDeviation) 1 = {2, 3, 5} ∧
      tightVal ε₁ ε₂ ε₃ 1 {2, 3, 5} = 2 - ε₁ - ε₂ := by sorry

end RoundRobinEq.SubmodularBluff
