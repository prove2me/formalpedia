-- Prove2me | Theorems.Thm_StartupLaunch_Strategy_proposition_1_i_iii
-- name    : StartupLaunch.Strategy.proposition_1_i_iii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:14:57.260991+00:00
-- url     : https://prove2.me/theorems/1dfacfdd-02cc-445b-b819-a9e846430800
-- title:
--   Proposition 1 (i)–(iii), p. 10 (PDF 11) — the established firm's strategy is given by two success-probability thresholds p1 ≤ p2
-- statement:
--   Under the standing assumptions $0 < v_o \le v_a$, $v_o < c$, $0 < \delta < 1$, $0 \le \alpha \le 1$, there exist thresholds $p_1 \le p_2$ on the per-period success probability such that, for every $q \in [0,1]$:
--
--   1. if $q \le p_1$, the established firm launches the on-hand product and discontinues the development of the advanced product: $\Pi_0 = \Pi_1 = \Pi_{LS} = V_o$;
--   2. if $p_1 < q \le p_2$, it launches the on-hand product and continues the development until it succeeds: $\Pi_0 = \Pi_{LC}$ and $\Pi_1 = \Pi_{LC}$;
--   3. if $q > p_2$, it does not launch the on-hand product and continues the development: $\Pi_0 = \Pi_{DC}$.
--
--   Here each identity is required of every solution $(\Pi_0,\Pi_1)$ of (1)–(2) at success probability $q$. This is the benchmark the startup's strategy is compared with, and the thresholds $p_1, p_2$ are the ones Proposition 2 refers to.
--
--   **Formalization Note.** The thresholds are characterized by the strategy they induce, not by closed forms; they are normalized to $p_1 \le 1$, with $p_2 = 1$ whenever $p_1 = 1$. "Until it succeeds" is read as the launched firm's value also being attained by continuing ($\Pi_1 = \Pi_{LC}$); for deferral the state does not change, so $\Pi_0 = \Pi_{DC}$ already expresses repetition. Part (iv) (comparative statics of $p_1, p_2$) is not part of this statement.
-- source:
--   Bhaskaran, Erzurumlu & Ramachandran, Sequential product development and introduction by cash-constrained start-ups, SSRN 3255345 (manuscript of February 2020), p. 10 (PDF 11), Proposition 1 (i)–(iii)

import Mathlib
import Definitions.Def_StartupLaunch_Strategy_Model

namespace StartupLaunch.Strategy

theorem proposition_1_i_iii (P : Params) (hP : P.Standing) :
    ∃ p1 p2 : ℝ, IsThresholds P p1 p2 := by sorry

end StartupLaunch.Strategy
