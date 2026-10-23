-- Prove2me | Theorems.Thm_StartupLaunch_Strategy_proposition_2_i_ii
-- name    : StartupLaunch.Strategy.proposition_2_i_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:15:02.727393+00:00
-- url     : https://prove2.me/theorems/5aa3534c-8d57-4887-96a8-0a975d3cd9a7
-- title:
--   Proposition 2 (i)–(ii), p. 16 (PDF 17) — below p1 or without cash the startup launches and stops; for p1 ≤ p < p2 with cash it launches and keeps developing
-- statement:
--   Assume the standing assumptions $0 < v_o \le v_a$, $v_o < c$, $0 < \delta < 1$, $0 \le \alpha \le 1$. Let $p \in [0,1]$ be the per-period success probability of the advanced product, $p_1 \le p_2$ thresholds of the established firm as in Proposition 1, $(R_0,R_1)$ the startup's value functions (solution of (3)–(5) with $R_I(E) - E$ bounded), and $E \ge 0$ the startup's cash.
--
--   1. If $p < p_1$ or $c > E + v_o$, the startup launches the on-hand product and discontinues the development of the advanced product: launching and stopping is strictly optimal,
--   $$R_0(E) = R_{LS}(E),\qquad R_{DC}(E) < R_{LS}(E),\qquad R_{LC}(E) < R_{LS}(E)\ \text{ whenever } c \le E + v_o .$$
--   2. If $p_1 \le p < p_2$ and $c < E + v_o$, the startup launches the on-hand product and continues the development of the advanced product:
--   $$R_0(E) = R_{LC}(E),\qquad\text{and}\qquad R_1(E') = R_{LC}(E')\ \text{ for every } E' \ge 0 \text{ with } c \le E' + v_o .$$
--
--   The startup thus follows the established firm when development is unlikely to succeed, and is forced to stop when it cannot fund the period's development; in the intermediate range it, too, launches the on-hand product and keeps developing for as long as cash allows. The paper's third part, a cash threshold for $p \ge p_2$, is not included (see below).
--
--   **Formalization Note.** In (ii), "continues the development" is read as continuing being optimal after the launch at every funded cash level; at $p = p_1$, launching and continuing may tie with launching and stopping, so (ii) asserts attainment, not strict optimality. Proposition 2(iii) is false and omitted: with $v_o = 6/5$, $v_a = 6$, $c = 24/5$, $\delta = 15/16$, $\alpha = 27/100$ and $p = 8/25 > p_2 = 1/12$, deferring is strictly optimal at $E = 6$ and $E = 9$ but launching at $E = 7$, so no cash threshold $\bar E_L$ exists. The thresholds are any pair satisfying Proposition 1's characterization (normalized to $p_1 \le 1$), and the value functions are any solution of (3)–(5) with bounded $R_I(E) - E$; both exist and the value functions are unique.
-- source:
--   Bhaskaran, Erzurumlu & Ramachandran, Sequential product development and introduction by cash-constrained start-ups, SSRN 3255345 (manuscript of February 2020), p. 16 (PDF 17), Proposition 2 (i)–(ii); part (iii) is false and omitted

import Mathlib
import Definitions.Def_StartupLaunch_Strategy_Model

namespace StartupLaunch.Strategy

theorem proposition_2_i_ii (P : Params) (hP : P.Standing) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (p1 p2 : ℝ) (hth : IsThresholds P p1 p2) (R0 R1 : ℝ → ℝ) (hR : StartupBellman P p R0 R1)
    (E : ℝ) (hE : 0 ≤ E) :
    ((p < p1 ∨ E + P.vo < P.c) →
      R0 E = RLS P E ∧ RDC P p R0 E < RLS P E ∧ (P.c ≤ E + P.vo → RLC P p R1 E < RLS P E)) ∧
    ((p1 ≤ p ∧ p < p2 ∧ P.c < E + P.vo) →
      R0 E = RLC P p R1 E ∧ ∀ E' : ℝ, 0 ≤ E' → P.c ≤ E' + P.vo → R1 E' = RLC P p R1 E') := by sorry

end StartupLaunch.Strategy
